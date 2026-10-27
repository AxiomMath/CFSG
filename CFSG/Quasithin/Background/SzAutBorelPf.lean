module

public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.Quasithin.Background.SzAutBorel

public section

namespace CFSG.Quasithin.SzAutBorelPf

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Suzuki (suzukiFrob_pow_four_ne_one)
open CFSG.ShultStronglyClosedTI (suzukiU_layer_kernel)

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem inner_of_torus_trivial (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (γ : MulAut (suzukiGroup a K))
    (hγU : (suzukiU a K).map γ.toMonoidHom = suzukiU a K)
    (hγD : ∀ l : Kˣ, (suzukiDElt a K l)⁻¹ * γ (suzukiDElt a K l) ∈ suzukiU a K) :
    ∃ y : suzukiGroup a K, γ = MulAut.conj y := by
  classical
  obtain ⟨hchar, ⟨φ, hφ⟩, -⟩ := suzuki_frobenius_exponents a K hK
  let _ : Module (ZMod 2) K := (ZMod.algebra K 2).toModule
  have hφ4 := suzukiFrob_pow_four_ne_one ha hK φ hφ
  obtain ⟨hΨfst, hΨrange, hΨres, -⟩ :=
    suzuki_two_A_automorphism_solvable (K := K) (by omega : 1 ≤ 2 * a + 1) hK φ hφ4
  obtain ⟨ι, hι, hιsymm, -⟩ := Suzuki_root_A_isomorphism hK φ hφ
  set r : MulAut (suzukiU a K) :=
    (γ.subgroupMap (suzukiU a K)).trans (MulEquiv.subgroupCongr hγU) with hrdef
  have hr : ∀ y : suzukiU a K, ((r y : suzukiU a K) : suzukiGroup a K) = γ y := fun y => rfl
  set α := MulAut.congr ι r
  have hαapply : ∀ p, α p = ι (r (ι.symm p)) := fun p => rfl
  obtain ⟨c, σ, hcσ⟩ : ∃ (c : Kˣ) (σ : K ≃+* K), ∀ x,
      (suzukiQuotAction α : K →ₗ[ZMod 2] K) x = c * σ x := by
    have hmem : suzukiQuotAction α ∈ Set.range (suzukiQuotAction (K := K) (φ := φ)) := ⟨_, rfl⟩
    rw [hΨrange] at hmem
    exact hmem
  have hfst : ∀ u v : K, ∃ w : K, γ (suzukiSElt a K u v) = suzukiSElt a K (c * σ u) w := by
    intro u v
    obtain ⟨u', w, huw⟩ := (mem_suzukiU_iff hK).1
      (r ⟨suzukiSElt a K u v, suzukiSElt_mem_suzukiU a K u v⟩).2
    refine ⟨w, ?_⟩
    rw [← hr ⟨suzukiSElt a K u v, suzukiSElt_mem_suzukiU a K u v⟩, ← huw]
    have e1 : r ⟨suzukiSElt a K u v, suzukiSElt_mem_suzukiU a K u v⟩ =
        ⟨suzukiSElt a K u' w, suzukiSElt_mem_suzukiU a K u' w⟩ := Subtype.ext huw.symm
    have e2 := hΨfst α (ι ⟨suzukiSElt a K u v, suzukiSElt_mem_suzukiU a K u v⟩)
    rw [hαapply, MulEquiv.symm_apply_apply, e1] at e2
    simp only [hι, hcσ] at e2
    exact congrArg₂ (suzukiSElt a K) e2.symm rfl
  have hkey : ∀ l : Kˣ, ((l⁻¹ : Kˣ) : K) * c = c * σ ((l⁻¹ : Kˣ) : K) := by
    intro l
    obtain ⟨t1, t2, ht⟩ := (mem_suzukiU_iff hK).1 (hγD l)
    have hγd : γ (suzukiDElt a K l) = suzukiDElt a K l * suzukiSElt a K t1 t2 := by
      rw [ht, mul_inv_cancel_left]
    obtain ⟨w1, hw1⟩ := hfst 1 0
    obtain ⟨w2, hw2⟩ := hfst ((l⁻¹ : Kˣ) : K) 0
    have hconj := suzukiDElt_conj' hK l 1 0
    rw [mul_one, mul_zero] at hconj
    have h := congrArg γ hconj
    rw [map_mul, map_mul, map_inv, hγd, hw1, hw2, map_one] at h
    rw [show suzukiDElt a K l * suzukiSElt a K t1 t2 * suzukiSElt a K (c * 1) w1 *
        (suzukiDElt a K l * suzukiSElt a K t1 t2)⁻¹ = suzukiDElt a K l *
        (suzukiSElt a K t1 t2 * suzukiSElt a K (c * 1) w1 * (suzukiSElt a K t1 t2)⁻¹) *
        (suzukiDElt a K l)⁻¹ by group] at h
    rw [suzukiSElt_inv hK, suzukiSElt_mul hK, suzukiSElt_mul hK, suzukiDElt_conj' hK] at h
    have h1 := (suzukiSElt_inj.1 h).1
    rw [show t1 + c * 1 + t1 = (c : K) by rw [mul_one, add_comm t1, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]] at h1
    exact h1
  have hσ : σ = 1 := by
    ext x
    rw [RingAut.one_apply]
    by_cases hx : x = 0
    · rw [hx, map_zero]
    · have h := hkey (Units.mk0 x hx)⁻¹
      rw [inv_inv, Units.val_mk0, mul_comm] at h
      exact (mul_left_cancel₀ c.ne_zero h).symm
  have hαq : ∀ x, (suzukiQuotAction α : K →ₗ[ZMod 2] K) x = c * (1 : K ≃+* K) x := by
    intro x
    rw [hcσ, hσ]
  have hαz := hΨres α c 1 hαq
  have hcθ : (c : K) * φ c = (c : K) ^ (2 ^ (a + 1) + 1) := by
    rw [hφ]
    exact (pow_succ' _ _).symm
  have hγZ0 : ∀ z : K, γ (suzukiSElt a K 0 z) =
      suzukiSElt a K 0 ((c : K) ^ (2 ^ (a + 1) + 1) * z) := by
    intro z
    have h0 : ∀ w : K, ((ι.symm ⟨0, w⟩ : suzukiU a K) : suzukiGroup a K) =
        suzukiSElt a K 0 w := by
      intro w
      rw [hιsymm, zero_pow (Nat.succ_ne_zero _), add_zero]
    have h1 := congrArg (fun p => ((ι.symm p : suzukiU a K) : suzukiGroup a K)) (hαz z)
    simp only [hαapply, MulEquiv.symm_apply_apply, hr, h0] at h1
    rw [h1, RingAut.one_apply, hcθ]
  set d := suzukiDElt a K c with hd
  set δ := MulAut.conj d * γ with hδ
  have hδapply : ∀ x, δ x = d * γ x * d⁻¹ := fun x => rfl
  have hδU : (suzukiU a K).map δ.toMonoidHom = suzukiU a K := by
    have hdU : (suzukiU a K).map (MulAut.conj d).toMonoidHom = suzukiU a K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1
        (suzukiT_le_normalizer hK (suzukiDElt_mem_suzukiT a K c))
    rw [hδ, show (MulAut.conj d * γ).toMonoidHom =
      (MulAut.conj d).toMonoidHom.comp γ.toMonoidHom from rfl, ← Subgroup.map_map, hγU, hdU]
  have hδZ : ∀ v ∈ suzukiZ0 a K, δ v = v := by
    intro v hv
    obtain ⟨z, rfl⟩ := (mem_suzukiZ0_iff hK).1 hv
    rw [hδapply, hγZ0, hd, suzukiDElt_conj' hK, mul_zero, Units.val_inv_eq_inv_val, inv_pow,
      inv_mul_cancel_left₀ (pow_ne_zero _ c.ne_zero)]
  have hδUZ : ∀ x ∈ suzukiU a K, x⁻¹ * δ x ∈ suzukiZ0 a K := by
    intro x hx
    obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
    obtain ⟨w, hw⟩ := hfst u v
    rw [hσ, RingAut.one_apply] at hw
    rw [hδapply, hw, hd, suzukiDElt_conj' hK, Units.val_inv_eq_inv_val,
      inv_mul_cancel_left₀ c.ne_zero, suzukiSElt_inv hK, suzukiSElt_mul hK, mem_suzukiZ0_iff hK]
    exact ⟨_, congrArg₂ (suzukiSElt a K) (CharTwo.add_self_eq_zero u).symm rfl⟩
  obtain ⟨b, -, hb⟩ := suzukiU_layer_kernel ha hK δ hδU hδZ hδUZ
  refine ⟨d⁻¹ * b, ?_⟩
  rw [map_mul, ← hb, hδ, map_inv, inv_mul_cancel_left]

theorem not_three_dvd_card (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ 3 ∣ Nat.card (suzukiGroup a K) := by
  rw [suzuki_order hK]
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    · omega
  · omega

theorem eq_one_of_conj_of_pow_three {G : Type} [Group G] [Finite G] (h3 : ¬ 3 ∣ Nat.card G)
    {γ : MulAut G} (hγ3 : γ ^ 3 = 1) {y : G} (hy : γ = MulAut.conj y) : γ = 1 := by
  have h1 : orderOf γ ∣ 3 := orderOf_dvd_of_pow_eq_one hγ3
  have h2 : orderOf γ ∣ Nat.card G := by
    rw [hy]
    exact (orderOf_map_dvd (MulAut.conj : G →* MulAut G) y).trans (orderOf_dvd_natCard y)
  rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ h2) h3

end CFSG.Quasithin.SzAutBorelPf

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.LieType.Ree SzAutBorelPf

theorem szAutBorelThree_holds : SzAutBorelThree := by
  intro X _ _ e hSz S α hα3 hαS hαB
  obtain ⟨-, a, ha, K, _, _, hfe, hK, ⟨ψ⟩⟩ := hSz
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfe]
  have hcard : Nat.card X = Nat.card (suzukiGroup a K) := Nat.card_congr ψ.toEquiv
  let P : Sylow 2 (suzukiGroup a K) := Sylow.ofCard ((S : Subgroup X).map ψ.toMonoidHom) (by
    rw [Subgroup.card_map_of_injective ψ.injective, Sylow.card_eq_multiplicity, hcard])
  let U₀ : Sylow 2 (suzukiGroup a K) :=
    Sylow.ofCard (suzukiU a K) (CFSG.RankThree.card_suzukiU_eq hK')
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (suzukiGroup a K) P U₀
  set ψ' : X ≃* suzukiGroup a K := ψ.trans (MulAut.conj g) with hψ'
  have hmem : ∀ x : X, x ∈ (S : Subgroup X) ↔ ψ' x ∈ suzukiU a K := by
    intro x
    have h1 : ((g • P : Sylow 2 (suzukiGroup a K)) : Subgroup (suzukiGroup a K)) =
        suzukiU a K := by rw [hg]; rfl
    rw [← h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change _ ↔ (MulAut.conj g)⁻¹ (ψ' x) ∈ (S : Subgroup X).map ψ.toMonoidHom
    have hx : (MulAut.conj g)⁻¹ (ψ' x) = ψ x := (MulAut.conj g).symm_apply_apply (ψ x)
    rw [hx, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hαmem : ∀ x : X, x ∈ (S : Subgroup X) ↔ α.symm x ∈ (S : Subgroup X) := by
    intro x
    conv_lhs => rw [← hαS]
    rw [Subgroup.mem_map_equiv]
  set γ : MulAut (suzukiGroup a K) := MulAut.congr ψ' α with hγ
  have hγapply : ∀ y, γ y = ψ' (α (ψ'.symm y)) := fun y => rfl
  have hγU : (suzukiU a K).map γ.toMonoidHom = suzukiU a K := by
    ext y
    rw [Subgroup.mem_map_equiv]
    have : γ.symm y = ψ' (α.symm (ψ'.symm y)) := rfl
    rw [this, ← hmem, ← hαmem, hmem, MulEquiv.apply_symm_apply]
  have hγD : ∀ l : Kˣ, (suzukiDElt a K l)⁻¹ * γ (suzukiDElt a K l) ∈ suzukiU a K := by
    intro l
    set b := ψ'.symm (suzukiDElt a K l) with hb
    have hbN : b ∈ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hD := (Subgroup.mem_normalizer_iff.1
        (suzukiT_le_normalizer hK' (suzukiDElt_mem_suzukiT a K l))) (ψ' x)
      rw [hmem, hmem, map_mul, map_mul, map_inv, hb, MulEquiv.apply_symm_apply]
      exact hD
    have h := (hmem _).1 (hαB b hbN)
    rw [map_mul, map_inv, hb, MulEquiv.apply_symm_apply] at h
    rw [hγapply]
    exact h
  have hγ3 : γ ^ 3 = 1 := by
    rw [hγ, ← map_pow, hα3, map_one]
  obtain ⟨y, hy⟩ := inner_of_torus_trivial ha hK' γ hγU hγD
  have hγ1 := eq_one_of_conj_of_pow_three (not_three_dvd_card hK') hγ3 hy
  rw [hγ] at hγ1
  exact (MulEquiv.map_eq_one_iff (MulAut.congr ψ')).1 hγ1

end CFSG.Quasithin
