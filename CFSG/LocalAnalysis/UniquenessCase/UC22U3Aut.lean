module

public import CFSG.LocalAnalysis.UniquenessCase.UC22U3Elt
public import CFSG.LocalAnalysis.UniquenessCase.UCKPSyl3
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.U3Aut

open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.Bender.Frame
open CFSG.RankThree.Classical CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.Coordinator

variable {k : ℕ} {E : Type} [Field E]

private theorem lemmaF (hU : UnitaryFieldData 2 k E) (hk : 2 ≤ k) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpk : p ∣ 2 ^ k + 1)
    {J : Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))} (hJ : ∀ x ∈ J, x ^ p = 1) :
    Nat.card J ≤ p ^ 2 ∧ (p ^ 2 ≤ Nat.card J → ∃ t ∈ J, t ≠ 1 ∧
      ∃ c : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E), orderOf c = 3 ∧ c * t = t * c) := by
  classical
  haveI := hU.finite
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by omega
  have hv := UCK.isOrthonormalFrame_single (p := 2) hU
  obtain ⟨k', hk'⟩ : ∃ k', 2 ^ k = k' + 1 :=
    ⟨2 ^ k - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
  have e : CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ k) E) ≃*
      primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E) :=
    CFSG.ComponentClassification.Burgoyne.U.uTransport hU (by norm_num)
  have hcard : Nat.card (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) * Nat.gcd 3 (k' + 2) =
      (k' + 1) ^ 3 * (k' * (k' + 2)) * ((k' + 2) * (k' ^ 2 + k' + 1)) := by
    have h := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSU_three_mul hU
    rw [← Nat.card_congr e.toEquiv, show k' + 2 = 2 ^ k + 1 by omega, h, hk',
      show (k' + 1) ^ 2 - 1 = k' * (k' + 2) from Nat.sub_eq_of_eq_add (by ring)]
    ring
  obtain ⟨T, hTF, hTq, hTidx, -⟩ :=
    UCK.exists_frame_sylow hU hk hk' hp3 (by rwa [show k' + 2 = 2 ^ k + 1 by omega]) hcard
  obtain ⟨-, -, hcomm, -, -, -, -⟩ := frame_group_structure hU hk hv
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := rootsOfUnity (2 ^ k + 1) E) p
    (by rw [card_rootsOfUnity_eq hU]; exact hpk)
  have hzp : z ^ p = 1 := hz ▸ pow_orderOf_eq_one z
  obtain ⟨ℓ₂, hℓ₂⟩ := UCK.exists_frameEigHom_eq hv _ (UCK.prod_line_eq_one z 2)
  obtain ⟨ℓ₁, hℓ₁⟩ := UCK.exists_frameEigHom_eq hv _ (UCK.prod_line_eq_one z 1)
  have hℓp : ∀ (j : Fin 3) (ℓ : frameTorusSU hU (fun i => Pi.single i 1)),
      (∀ l, frameEigHom hv l ℓ = if l = j then z ^ (-2 : ℤ) else z) →
      (QuotientGroup.mk (ℓ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
        primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ^ p = 1 := by
    intro j ℓ hℓ
    have hℓ1 : ℓ ^ p = 1 := frameTorusSU_ext hv fun l => by
      rw [map_pow, hℓ, map_one]
      split_ifs
      · rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hzp,
          _root_.one_zpow]
      · exact hzp
    rw [← QuotientGroup.mk_pow, ← Subgroup.coe_pow, hℓ1]
    rfl
  set L₁ : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E) :=
    QuotientGroup.mk (ℓ₁ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) with hL₁
  set L₂ : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E) :=
    QuotientGroup.mk (ℓ₂ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) with hL₂
  have hc12 : Commute L₂ L₁ :=
    hcomm _ (Subgroup.mem_map_of_mem _ ℓ₂.2) _ (Subgroup.mem_map_of_mem _ ℓ₁.2)
  have hnat : ∀ L : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E), L ^ p = 1 → ∀ m : ℤ,
      ∃ α : Fin p, L ^ m = L ^ (α : ℕ) := by
    intro L hL m
    have h0 := Int.emod_nonneg m (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos m (by exact_mod_cast hp.pos : (0 : ℤ) < p)
    refine ⟨⟨(m % (p : ℤ)).toNat, by omega⟩, ?_⟩
    rw [zpow_eq_zpow_emod' m hL, ← zpow_natCast, Int.toNat_of_nonneg h0]
  have hrep : ∀ t ∈ frameTorus hU (fun i => Pi.single i 1), t ^ p = 1 →
      ∃ αβ : Fin p × Fin p, t = L₂ ^ (αβ.1 : ℕ) * L₁ ^ (αβ.2 : ℕ) := by
    intro t ht htp
    obtain ⟨d, hdT, rfl, hdq⟩ := UCK.exists_lift_pow_eq_one hp hp3 ht htp
    have hDq : (⟨d, hdT⟩ : frameTorusSU hU (fun i => Pi.single i 1)) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hdq)
    haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨a, ha⟩ := UCK.exists_pow_eq_of_pow_eq_one hz (a := frameEigHom hv 0 ⟨d, hdT⟩)
      (by rw [← map_pow, hDq, map_one])
    obtain ⟨b, hb⟩ := UCK.exists_pow_eq_of_pow_eq_one hz (a := frameEigHom hv 1 ⟨d, hdT⟩)
      (by rw [← map_pow, hDq, map_one])
    have hd3 := UCK.pow_three_eq_lines hv hℓ₁ hℓ₂ ha.symm hb.symm
    have ht3 : (QuotientGroup.mk d : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ^ 3 =
        L₂ ^ (2 * (a : ℤ) + b) * L₁ ^ ((a : ℤ) - b) := by
      have h1 := congrArg (fun y : frameTorusSU hU (fun i => Pi.single i 1) => (QuotientGroup.mk
        (y : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : primeFormP hU
          (1 : Matrix (Fin 3) (Fin 3) E))) hd3
      simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_zpow, QuotientGroup.mk_pow,
        QuotientGroup.mk_mul, QuotientGroup.mk_zpow] using h1
    obtain ⟨s, u, hu⟩ := UCK.exists_three_dvd_mul_add_one hp hp3
    have htu : (QuotientGroup.mk d : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) =
        ((QuotientGroup.mk d : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ^ 3) ^ u := by
      rw [← pow_mul, ← hu, pow_succ, pow_mul, htp, one_pow, one_mul]
    obtain ⟨α, hα⟩ := hnat L₂ (hℓp 2 ℓ₂ hℓ₂) ((2 * (a : ℤ) + b) * u)
    obtain ⟨β, hβ⟩ := hnat L₁ (hℓp 1 ℓ₁ hℓ₁) (((a : ℤ) - b) * u)
    refine ⟨(α, β), ?_⟩
    rw [htu, ht3, ((hc12.zpow_zpow _ _).mul_pow u), ← zpow_natCast (L₂ ^ _),
      ← zpow_natCast (L₁ ^ _), ← _root_.zpow_mul, ← _root_.zpow_mul, hα, hβ]
  have hJp : IsPGroup p J := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hJ x x.2)⟩
  obtain ⟨S, hJS⟩ := hJp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))
    (hTq.toSylow hTidx) S
  have hgT : ∀ x ∈ J, ∃ t ∈ T, g * t * g⁻¹ = x := fun x hx => by
    have h1 : x ∈ ((g • hTq.toSylow hTidx : Sylow p _) : Subgroup _) := hg ▸ hJS hx
    rwa [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  have hJrep : ∀ x : J, ∃ αβ : Fin p × Fin p,
      (x : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) =
        g * (L₂ ^ (αβ.1 : ℕ) * L₁ ^ (αβ.2 : ℕ)) * g⁻¹ := by
    intro x
    obtain ⟨t, htT, hxt⟩ := hgT x x.2
    have htp : t ^ p = 1 := by
      have h1 := hJ x x.2
      rwa [← hxt, conj_pow, conj_eq_one_iff] at h1
    obtain ⟨αβ, hαβ⟩ := hrep t (hTF htT) htp
    exact ⟨αβ, by rw [← hxt, hαβ]⟩
  choose ι hι using hJrep
  have hιinj : Function.Injective ι := fun x y hxy => Subtype.ext (by rw [hι x, hι y, hxy])
  have hpp : Nat.card (Fin p × Fin p) = p ^ 2 := by rw [Nat.card_prod, Nat.card_fin, sq]
  refine ⟨hpp ▸ Nat.card_le_card_of_injective ι hιinj, fun hJc => ?_⟩
  obtain ⟨x, hx⟩ := (hιinj.bijective_of_nat_card_le (hpp.trans_le hJc)).2
    (⟨1, hp.one_lt⟩, ⟨0, hp.pos⟩)
  have hxL : (x : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) = g * L₂ * g⁻¹ := by
    rw [hι x, hx]
    simp
  have hL₂1 : L₂ ≠ 1 := fun h1 => by
    obtain ⟨s, hs3, hs⟩ := UCK.exists_eig_mul_of_mk_eq hv (d := 1) (d' := ℓ₂)
      (by rw [OneMemClass.coe_one, QuotientGroup.mk_one]; exact h1.symm)
    have h0 := hs 0
    rw [hℓ₂, map_one, one_mul, if_neg (by decide)] at h0
    have := Nat.le_of_dvd (by norm_num) (hz ▸ orderOf_dvd_of_pow_eq_one (h0 ▸ hs3 : z ^ 3 = 1))
    omega
  obtain ⟨c₀, hc₀, hc₀L⟩ := exists_orderOf_three_commute_line hU (d := ℓ₂) (by
    rw [hℓ₂, hℓ₂, if_neg (by decide), if_neg (by decide)])
  refine ⟨x, x.2, fun h => hL₂1 ?_, g * c₀ * g⁻¹, ?_, ?_⟩
  · rwa [hxL, conj_eq_one_iff] at h
  · exact (MulEquiv.orderOf_eq (MulAut.conj g) c₀).trans hc₀
  · rw [hxL]
    calc g * c₀ * g⁻¹ * (g * L₂ * g⁻¹) = g * (c₀ * L₂) * g⁻¹ := by group
      _ = g * (L₂ * c₀) * g⁻¹ := by rw [hc₀L]
      _ = g * L₂ * g⁻¹ * (g * c₀ * g⁻¹) := by group

theorem card_le_of_pow_eq_one (hU : UnitaryFieldData 2 k E) (hk : 2 ≤ k) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpk : p ∣ 2 ^ k + 1)
    {J : Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))} (hJ : ∀ x ∈ J, x ^ p = 1) :
    Nat.card J ≤ p ^ 2 :=
  (lemmaF hU hk hp hp5 hpk hJ).1

theorem exists_commute_orderOf_three (hU : UnitaryFieldData 2 k E) (hk : 2 ≤ k) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpk : p ∣ 2 ^ k + 1)
    {J : Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))} (hJ : ∀ x ∈ J, x ^ p = 1)
    (hJc : p ^ 2 ≤ Nat.card J) :
    ∃ t ∈ J, t ≠ 1 ∧ ∃ c : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E), orderOf c = 3 ∧
      c * t = t * c :=
  (lemmaF hU hk hp hp5 hpk hJ).2 hJc

theorem exists_fixed_eq_range (hU : UnitaryFieldData 2 k E) (hk : 2 ≤ k) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {β : MulAut (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))} (hβ : β ^ p = 1)
    (hβi : β ∉ (MulAut.conj : _ →* MulAut (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))).range) :
    p ∣ k ∧ ∃ (E₀ : Type) (_ : Field E₀) (h₀ : UnitaryFieldData 2 (k / p) E₀)
      (j : primeFormP h₀ (1 : Matrix (Fin 3) (Fin 3) E₀) →*
        primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)),
      Function.Injective j ∧ ∀ y, β y = y ↔ y ∈ j.range := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hne' : ¬(3 = 3 ∧ 2 ^ k = 2) := fun ⟨_, h⟩ => by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hC1 : IsPrimeFormGram (1 : GL (Fin 3) E) := isPrimeFormGram_one
  have hdiv' : ¬ p ∣ Nat.gcd 3 (2 ^ k + 1) := fun h =>
    absurd (Nat.le_of_dvd (by norm_num) (h.trans (Nat.gcd_dvd_left 3 _))) (by omega)
  have hβ1 : β ≠ 1 := fun h1 => hβi (h1 ▸ Subgroup.one_mem _)
  have hβord : orderOf β = p := orderOf_eq_prime hβ hβ1
  set σ := primeFormFieldFactor hU hC1 (le_refl 3) hne' β with hσdef
  have hσp : σ ^ p = 1 := by rw [hσdef, ← map_pow, hβ, map_one]
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    have hD : β ∈ primeFormD hU ((1 : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) := by
      rw [← ker_primeFormFieldFactor hU hC1 (le_refl 3) hne']
      exact hσ1
    exact hβi (mem_inner_of_mem_primeFormD hU (le_refl 3) hne' hp hdiv' hD hβ)
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    unitary_prime_semilinear_field_descent' hU (le_refl 3) hne' hp hp2 β hβord σ hσdef.symm hσord
  set u := primeFormConjHom hU ((1 : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) M with hu
  set fσ := primeFormFieldHom hU (isPrimeFormGram_one (n := 3)) σ with hfσ
  have hβu : β = u * fσ * u⁻¹ := by
    rw [← hM]
    group
  have hZ' : ¬ p ∣ Nat.card (normOneScalars hU
      (gramSU hU ((1 : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)) 3) := by
    rw [card_normOneScalars_one hU (by norm_num)]
    exact hdiv'
  obtain ⟨hpf, -, -, -, -, hinj, hrange, -, -, -, -⟩ :=
    prime_subfield_fixed_group_package hU hp hp2 hσord 3 (le_refl 3) hne' hZ'
  refine ⟨hpf, fixSubfield σ, inferInstance, fixSubfield_unitaryFieldData hU hp hp2 hσord,
    u.toMonoidHom.comp (primeSubfieldPSU hU hp hp2 hσord 3), u.injective.comp hinj, fun y => ?_⟩
  rw [hβu, MulAut.mul_apply, MulAut.mul_apply]
  constructor
  · intro hy
    have h1 : u⁻¹ y ∈ fieldFixedPSU hU 3 σ := by
      change fσ (u⁻¹ y) = u⁻¹ y
      calc fσ (u⁻¹ y) = u⁻¹ (u (fσ (u⁻¹ y))) := (MulAut.inv_apply_self _ u _).symm
        _ = u⁻¹ y := by rw [hy]
    rw [← hrange] at h1
    obtain ⟨x, hx⟩ := h1
    exact ⟨x, by rw [MonoidHom.comp_apply, hx, MulEquiv.coe_toMonoidHom, MulAut.apply_inv_self]⟩
  · rintro ⟨x, rfl⟩
    have h1 : primeSubfieldPSU hU hp hp2 hσord 3 x ∈ fieldFixedPSU hU 3 σ := hrange ▸ ⟨x, rfl⟩
    change fσ _ = _ at h1
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.inv_apply_self, h1,
      MonoidHom.id_apply]

theorem exists_fixed_orderOf_three (hU : UnitaryFieldData 2 k E) (hk : 2 ≤ k) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {β : MulAut (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))}
    (hβ : β ^ p = 1)
    (hβi : β ∉ (MulAut.conj : _ →* MulAut (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))).range) :
    ∃ c : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E), orderOf c = 3 ∧ β c = c := by
  obtain ⟨-, E₀, _, h₀, j, hj, hfix⟩ := exists_fixed_eq_range hU hk hp hp5 hβ hβi
  obtain ⟨w, hw⟩ := exists_orderOf_three h₀
  exact ⟨j w, by rw [orderOf_injective j hj, hw], (hfix (j w)).2 ⟨w, rfl⟩⟩

theorem exists_commute_orderOf_three_fixed (hU : UnitaryFieldData 2 k E) (hk : 2 ≤ k) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {β : MulAut (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))}
    (hβ : β ^ p = 1)
    (hβi : β ∉ (MulAut.conj : _ →* MulAut (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))).range)
    (hpk : p ∣ 2 ^ k + 1) {J : Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))}
    (hJ : ∀ x ∈ J, x ^ p = 1) (hJc : p ^ 2 ≤ Nat.card J) (hβJ : ∀ x ∈ J, β x = x) :
    ∃ t ∈ J, t ≠ 1 ∧ ∃ c : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E), orderOf c = 3 ∧
      c * t = t * c ∧ β c = c := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨m, hm⟩, E₀, _, h₀, j, hj, hfix⟩ := exists_fixed_eq_range hU hk hp hp5 hβ hβi
  have hkm : k / p = m := by rw [hm, Nat.mul_div_cancel_left m hp.pos]
  have hpm : p ∣ 2 ^ m + 1 := by
    rw [← ZMod.natCast_eq_zero_iff] at hpk ⊢
    push_cast at hpk ⊢
    rwa [hm, mul_comm p m, pow_mul, ZMod.pow_card] at hpk
  have hm2 : 2 ≤ m := by
    rcases (by omega : m = 0 ∨ m = 1 ∨ 2 ≤ m) with rfl | rfl | h
    · omega
    · exact absurd (Nat.le_of_dvd (by norm_num) hpm) (by norm_num; omega)
    · exact h
  have hJr : J ≤ j.range := fun x hx => (hfix x).1 (hβJ x hx)
  have hJ₀c : Nat.card (J.comap j) = Nat.card J := by
    rw [← Subgroup.card_map_of_injective hj, Subgroup.map_comap_eq_self hJr]
  have hJ₀p : ∀ x ∈ J.comap j, x ^ p = 1 := fun x hx =>
    hj (by rw [map_pow, hJ _ hx, map_one])
  obtain ⟨t, ht, ht1, c, hc, hct⟩ := exists_commute_orderOf_three h₀ (by rw [hkm]; exact hm2) hp
    hp5 (by rw [hkm]; exact hpm) hJ₀p (hJ₀c.symm ▸ hJc)
  refine ⟨j t, ht, fun h => ht1 (hj (h.trans (map_one j).symm)), j c, ?_, ?_,
    (hfix (j c)).2 ⟨c, rfl⟩⟩
  · rw [orderOf_injective j hj, hc]
  · rw [← map_mul, hct, map_mul]

end CFSG.LocalAnalysis.UniquenessCase.UC22.U3Aut
