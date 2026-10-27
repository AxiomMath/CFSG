module

public import CFSG.Quasithin.EmptyFaithful.S151CLDef
public import CFSG.Quasithin.EmptyFaithful.S152L25
public import CFSG.Quasithin.EmptyFaithful.S146xB2Aut
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem520
public import CFSG.Quasithin.Background.C1PackS15205E
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L33
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadL33
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma33
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
public import CFSG.Quasithin.Background.C1PackS15348

public section

namespace CFSG.Quasithin.S151L33

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.Fin253 CFSG.Quasithin

theorem card_lt_four_of_centralizes_odd {X : Type} [Group X] [Finite X] (hD : RadData X)
    {x : X} (hx1 : x ≠ 1) (hxo : Odd (orderOf x)) {R : Subgroup X} (hR2 : IsPGroup 2 ↥R)
    (hRx : ∀ r ∈ R, r * x = x * r) : Nat.card ↥R < 4 := by
  by_contra h4
  rcases exists_order_four_or_klein_of_pGroup hR2 (not_lt.mp h4) with
    ⟨u, huR, hu4⟩ | ⟨a, haR, b, hbR, ha1, hb1, hab, haa, hbb, hcab⟩
  · have hu4' : u * u * (u * u) = 1 := by
      have : u ^ 4 = 1 := hu4 ▸ pow_orderOf_eq_one u
      calc u * u * (u * u) = u ^ 4 := (pow_four_eq' u).symm
        _ = 1 := this
    have h := hD.odd_no4 x hx1 hxo u (hRx u huR) hu4'
    have : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hu4] at this
    omega
  · exact hD.odd_noV x hx1 hxo a b ha1 hb1 hab haa hbb hcab (hRx a haR) (hRx b hbR)

theorem false_of_sylow_normalizes_three {X : Type} [Group X] [Finite X] (hD : RadData X)
    {P : Subgroup X} (hP2 : IsPGroup 2 ↥P) (hP : 8 ≤ Nat.card ↥P) {x : X} (hx3 : orderOf x = 3)
    (hn : P ≤ Subgroup.normalizer (Subgroup.zpowers x : Set X)) : False := by
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx3
    omega
  have hxo : Odd (orderOf x) := by rw [hx3]; decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Subgroup X := Subgroup.zpowers x
  have hQcard : Nat.card Q = 3 := by
    rw [Nat.card_zpowers, hx3]
  have : IsCyclic Q := inferInstance
  have hAut : Nat.card (MulAut Q) = 2 := by
    rw [IsCyclic.card_mulAut, hQcard]
    decide
  let ψ : ↥P →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hn)
  have hmul : ψ.ker.index * Nat.card ψ.ker = Nat.card ↥P := Subgroup.index_mul_card ψ.ker
  rw [Subgroup.index_ker] at hmul
  have hrange : Nat.card ψ.range ≤ 2 := by
    have := Subgroup.card_le_card_group ψ.range
    omega
  have hker8 : 4 ≤ Nat.card ψ.ker := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥P ≤ 2 * 3 := by
      rw [← hmul]
      exact Nat.mul_le_mul hrange (by omega)
    omega
  let R : Subgroup X := ψ.ker.map P.subtype
  have hRcard : Nat.card R = Nat.card ψ.ker := Subgroup.card_map_of_injective P.subtype_injective
  have hR2 : IsPGroup 2 ↥R := hP2.to_le (Subgroup.map_subtype_le _)
  have hRx : ∀ r ∈ R, r * x = x * r := by
    rintro _ ⟨p, hp, rfl⟩
    have h1 : ψ p = 1 := hp
    have h2 := congrArg (fun φ : MulAut Q => ((φ ⟨x, Subgroup.mem_zpowers x⟩ : Q) : X)) h1
    have h3 : ((ψ p ⟨x, Subgroup.mem_zpowers x⟩ : Q) : X) = (p : X) * x * (p : X)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe Q (Subgroup.inclusion hn p)
        ⟨x, Subgroup.mem_zpowers x⟩
    have h4 : (p : X) * x * (p : X)⁻¹ = x := by
      simpa [h3] using h2
    show (p : X) * x = x * (p : X)
    calc (p : X) * x = ((p : X) * x * (p : X)⁻¹) * p := by group
      _ = x * p := by rw [h4]
  have := card_lt_four_of_centralizes_odd hD hx1 hxo hR2 hRx
  omega


theorem card_sylow_sixteen {X : Type} [Group X] [Finite X] (hD : RadData X) {P : Subgroup X}
    (hP : IsSylowTwoOf P ⊤) : Nat.card P = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, -, hcard⟩ := hD.card
  obtain ⟨a, ha⟩ := hP.isPGroup.exists_card_eq
  have hidx : ¬ 2 ∣ P.index := by
    have h2 := hP.2.2
    rwa [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right _] at h2
  have hmul := Subgroup.card_mul_index P
  rw [ha, hcard] at hmul
  have hcop1 : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have hdvd1 : 2 ^ a ∣ 16 := hcop1.dvd_of_dvd_mul_right ⟨P.index, hmul.symm ▸ rfl⟩
  have hcop2 : Nat.Coprime 16 P.index :=
    Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega)))
  have hdvd2 : 16 ∣ 2 ^ a := hcop2.dvd_of_dvd_mul_right ⟨m, hmul⟩
  have h1 : a ≤ 4 := by
    have := Nat.le_of_dvd (by norm_num) hdvd1
    by_contra hlt
    have : 2 ^ 5 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2 : 4 ≤ a := by
    have := Nat.le_of_dvd (by positivity) hdvd2
    by_contra hlt
    have : 2 ^ a ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [ha, show a = 4 by omega]
  norm_num


theorem exists_order_three {Λ : Type} [Group Λ] {F A : Subgroup Λ} (hAo : A = oTwoUpper A)
    (hAc : ¬ A ≤ Subgroup.centralizer (F : Set Λ)) (hAF : A ≤ Subgroup.normalizer (F : Set Λ))
    (hN : Nat.card (Subgroup.normalizer (F : Set Λ)) = 24) :
    ∃ x ∈ A, orderOf x = 3 ∧ x ∉ Subgroup.centralizer (F : Set Λ) := by
  by_contra hcon
  push Not at hcon
  apply hAc
  conv_lhs => rw [hAo]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxA, hxodd⟩
  by_contra hxc
  have hxN : x ∈ Subgroup.normalizer (F : Set Λ) := hAF hxA
  have hdvd : orderOf x ∣ 24 := by
    have := orderOf_dvd_natCard (⟨x, hxN⟩ : ↥(Subgroup.normalizer (F : Set Λ)))
    rwa [Subgroup.orderOf_mk, hN] at this
  have hcop : Nat.Coprime (orderOf x) 8 := by
    exact Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hxodd)
  have h3 : orderOf x ∣ 3 := hcop.dvd_of_dvd_mul_left (by simpa using hdvd)
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h3'
  · apply hxc
    rw [orderOf_eq_one_iff.mp h1]
    exact Subgroup.one_mem _
  · exact hxc (hcon x hxA h3')


@[expose] def V4set : Finset (Perm (Fin 4)) :=
  Finset.univ.filter fun σ => σ * σ = 1 ∧ Perm.sign σ = 1

theorem card_V4set : V4set.card = 4 := by decide +kernel

theorem conj_class_big : ∀ τ : Perm (Fin 4), τ * τ = 1 → Perm.sign τ = -1 →
    5 ≤ (Finset.univ.image fun g : Perm (Fin 4) => g * τ * g⁻¹).card := by decide +kernel

@[expose] def pairProp (a b : Perm (Fin 4)) : Prop :=
  a ^ 3 = 1 → b ^ 3 = 1 → a ≠ 1 → b ≠ 1 → b ≠ a → b ≠ a⁻¹ →
    ∀ σ ∈ V4set, σ = 1 ∨ σ = a * b * a⁻¹ * b⁻¹ ∨ σ = a * (a * b * a⁻¹ * b⁻¹) * a⁻¹ ∨
      σ = a * a * (a * b * a⁻¹ * b⁻¹) * a⁻¹ * a⁻¹

instance (a b : Perm (Fin 4)) : Decidable (pairProp a b) := by unfold pairProp; infer_instance

theorem pair_lemma : ∀ a b : Perm (Fin 4), pairProp a b := by decide +kernel

section Inner

variable {Ñ : Type} [Group Ñ]

theorem sign_eq_one_of_normal (Φ : Ñ ≃* Perm (Fin 4)) {F' : Subgroup Ñ} [F'.Normal]
    (hF4 : Nat.card F' = 4) (hF2 : ∀ f ∈ F', f * f = 1) {f : Ñ} (hf : f ∈ F') :
    Perm.sign (Φ f) = 1 := by
  classical
  by_contra hne
  have hneg : Perm.sign (Φ f) = -1 := by
    rcases Int.units_eq_one_or (Perm.sign (Φ f)) with h | h
    · exact absurd h hne
    · exact h
  have hτ : Φ f * Φ f = 1 := by rw [← map_mul, hF2 f hf, map_one]
  have h5 := conj_class_big (Φ f) hτ hneg
  set Fh : Subgroup (Perm (Fin 4)) := F'.map Φ.toMonoidHom with hFh
  have hcard : Nat.card Fh = 4 := by
    rw [hFh, Subgroup.card_map_of_injective Φ.injective, hF4]
  have hsub : (Finset.univ.image fun g : Perm (Fin 4) => g * Φ f * g⁻¹) ⊆
      Finset.univ.filter fun σ => σ ∈ Fh := by
    intro σ hσ
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hσ
    obtain ⟨g, rfl⟩ := hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Φ.symm g * f * (Φ.symm g)⁻¹, ?_, ?_⟩
    · exact Subgroup.Normal.conj_mem inferInstance f hf _
    · simp
  have hle := Finset.card_le_card hsub
  have hfc : (Finset.univ.filter fun σ => σ ∈ Fh).card = Nat.card Fh := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  omega

theorem mem_of_sq_one_of_sign (Φ : Ñ ≃* Perm (Fin 4)) {F' : Subgroup Ñ} [F'.Normal]
    (hF4 : Nat.card F' = 4) (hF2 : ∀ f ∈ F', f * f = 1) {n : Ñ} (hn : n * n = 1)
    (hs : Perm.sign (Φ n) = 1) : n ∈ F' := by
  classical
  set Fh : Subgroup (Perm (Fin 4)) := F'.map Φ.toMonoidHom with hFh
  have hcard : Nat.card Fh = 4 := by
    rw [hFh, Subgroup.card_map_of_injective Φ.injective, hF4]
  have hfc : (Finset.univ.filter fun σ => σ ∈ Fh).card = Nat.card Fh := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsubset : (Finset.univ.filter fun σ => σ ∈ Fh) ⊆ V4set := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨f, hf, rfl⟩ := hσ
    simp only [V4set, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by rw [← map_mul, hF2 f hf, map_one], sign_eq_one_of_normal Φ hF4 hF2 hf⟩
  have heq := Finset.eq_of_subset_of_card_le hsubset (by rw [hfc, hcard, card_V4set])
  have hmem : Φ n ∈ V4set := by
    simp only [V4set, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by rw [← map_mul, hn, map_one], hs⟩
  rw [← heq] at hmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨f, hf, hfn⟩ := hmem
  have : f = n := Φ.injective hfn
  exact this ▸ hf

theorem sign_eq_one_of_oTwoUpper (Φ : Ñ ≃* Perm (Fin 4)) {A' : Subgroup Ñ} (hA : A' = oTwoUpper A')
    {a : Ñ} (ha : a ∈ A') : Perm.sign (Φ a) = 1 := by
  have hle : oTwoUpper A' ≤ (Perm.sign.comp Φ.toMonoidHom).ker := by
    refine oTwoUpper_le_of_pow_mem fun x _ => ⟨1, ?_⟩
    rw [MonoidHom.mem_ker, pow_one]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [pow_two, map_mul, map_mul, Int.units_mul_self]
  have h2 : (Perm.sign.comp Φ.toMonoidHom) a = 1 := MonoidHom.mem_ker.mp (hle (hA ▸ ha))
  exact h2

theorem F_le_A (Φ : Ñ ≃* Perm (Fin 4)) {F' A' : Subgroup Ñ} [F'.Normal]
    (hF4 : Nat.card F' = 4) (hF2 : ∀ f ∈ F', f * f = 1) {x y : Ñ} (hx : x ∈ A') (hy : y ∈ A')
    (hx3 : orderOf x = 3) (hy3 : orderOf y = 3) (hxy : y ∉ Subgroup.zpowers x) : F' ≤ A' := by
  intro f hf
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx3
  have hy1 : y ≠ 1 := by
    rintro rfl
    simp at hy3
  have hyx : y ≠ x := fun h => hxy (h ▸ Subgroup.mem_zpowers x)
  have hyx' : y ≠ x⁻¹ := fun h => hxy (h ▸ Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  have hx3' : x ^ 3 = 1 := hx3 ▸ pow_orderOf_eq_one x
  have hy3' : y ^ 3 = 1 := hy3 ▸ pow_orderOf_eq_one y
  have hσ : Φ f ∈ V4set := by
    simp only [V4set, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by rw [← map_mul, hF2 f hf, map_one], sign_eq_one_of_normal Φ hF4 hF2 hf⟩
  have key := pair_lemma (Φ x) (Φ y) (by rw [← map_pow, hx3', map_one])
    (by rw [← map_pow, hy3', map_one])
    (fun h => hx1 (Φ.injective (h.trans (map_one Φ).symm)))
    (fun h => hy1 (Φ.injective (h.trans (map_one Φ).symm)))
    (fun h => hyx (Φ.injective h)) (fun h => hyx' (Φ.injective (by rw [h, map_inv]))) (Φ f) hσ
  have hc : x * y * x⁻¹ * y⁻¹ ∈ A' := by
    exact A'.mul_mem (A'.mul_mem (A'.mul_mem hx hy) (A'.inv_mem hx)) (A'.inv_mem hy)
  rcases key with h | h | h | h
  · rw [Φ.injective (h.trans (map_one Φ).symm)]
    exact A'.one_mem
  · have : f = x * y * x⁻¹ * y⁻¹ := Φ.injective (by rw [h]; simp)
    rw [this]; exact hc
  · have : f = x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ := Φ.injective (by rw [h]; simp)
    rw [this]; exact A'.mul_mem (A'.mul_mem hx hc) (A'.inv_mem hx)
  · have : f = x * x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ * x⁻¹ := Φ.injective (by rw [h]; simp)
    rw [this]
    exact A'.mul_mem (A'.mul_mem (A'.mul_mem (A'.mul_mem hx hx) hc) (A'.inv_mem hx)) (A'.inv_mem hx)

end Inner


theorem ffl
    {Λ : Type} [Group Λ] [Finite Λ]
    (h : CFSG.Open.StatedClassicalModel Λ CFSG.Open.StatedLieTag.PSL 3 3 1) {P F A : Subgroup Λ}
    (hP : IsSylowTwoOf P ⊤) (hF : IsFourSubgroup F) (hAo : A = oTwoUpper A)
    (hAF : A ≤ Subgroup.normalizer (F : Set Λ)) (hAc : ¬ A ≤ Subgroup.centralizer (F : Set Λ))
    (hPA : P ≤ Subgroup.normalizer (A : Set Λ)) : False := by
  have hfacts : SmallListFacts Λ := (Unc25L33.l33_facts Λ h).1
  have hD : RadData Λ := radData_of_stated_l33 h
  have hP16 : Nat.card P = 16 := card_sylow_sixteen hD hP
  have hP2 : IsPGroup 2 ↥P := hP.isPGroup
  obtain ⟨Φ⟩ := hfacts.four_normalizer F hF
  set N : Subgroup Λ := Subgroup.normalizer (F : Set Λ) with hN
  have hNcard : Nat.card N = 24 := by
    rw [Nat.card_congr Φ.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  obtain ⟨x, hxA, hx3, hxc⟩ := exists_order_three hAo hAc hAF hNcard
  by_cases hn : P ≤ Subgroup.normalizer (Subgroup.zpowers x : Set Λ)
  · exact false_of_sylow_normalizes_three hD hP2 (by omega) hx3 hn
  ·
    obtain ⟨p, hp, hpx⟩ : ∃ p ∈ P, p * x * p⁻¹ ∉ Subgroup.zpowers x := by
      by_contra hcon
      push Not at hcon
      apply hn
      intro p hp
      refine A4.mem_normalizer_of_conj_mem fun k hk => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      have : p * x ^ n * p⁻¹ = (p * x * p⁻¹) ^ n := by
        have := map_zpow (MulAut.conj p) x n
        simp only [MulAut.conj_apply] at this
        exact this
      rw [this]
      exact Subgroup.zpow_mem _ (hcon p hp) n
    set y : Λ := p * x * p⁻¹ with hy
    have hyA : y ∈ A := (Subgroup.mem_normalizer_iff.mp (hPA hp) x).mp hxA
    have hy3 : orderOf y = 3 := by
      rw [hy, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hx3
    have hFN : F ≤ N := Subgroup.le_normalizer
    have hFnormal : (F.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hFN).mpr le_rfl
    have hF4 : Nat.card (F.subgroupOf N) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv]
      exact hF.2
    have hF2 : ∀ f ∈ F.subgroupOf N, f * f = 1 := by
      intro f hf
      have h1 : ((f : N) : Λ) ^ 2 = 1 := hF.1.2 _ hf
      apply Subtype.ext
      simpa [pow_two] using h1
    have hAo' : A.subgroupOf N = oTwoUpper (A.subgroupOf N) := by
      rw [A4.oTwoUpper_subgroupOf hAF, ← hAo]
    have hxN : x ∈ N := hAF hxA
    have hyN : y ∈ N := hAF hyA
    have hxy : (⟨y, hyN⟩ : N) ∉ Subgroup.zpowers (⟨x, hxN⟩ : N) := by
      intro hmem
      apply hpx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    have hFA' : F.subgroupOf N ≤ A.subgroupOf N :=
      F_le_A Φ hF4 hF2 (x := ⟨x, hxN⟩) (y := ⟨y, hyN⟩) hxA hyA
        (by rw [← Subgroup.orderOf_mk x hxN] at hx3; exact hx3)
        (by rw [← Subgroup.orderOf_mk y hyN] at hy3; exact hy3) hxy
    have hFA : F ≤ A := fun f hf => hFA' (show (⟨f, hFN hf⟩ : N) ∈ F.subgroupOf N from hf)
    have hPN : P ≤ N := by
      intro p' hp'
      refine A4.mem_normalizer_of_conj_mem fun f hf => ?_
      have hqA : p' * f * p'⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hPA hp') f).mp (hFA hf)
      have hqN : p' * f * p'⁻¹ ∈ N := hAF hqA
      have hq2 : (⟨p' * f * p'⁻¹, hqN⟩ : N) * ⟨p' * f * p'⁻¹, hqN⟩ = 1 := by
        apply Subtype.ext
        have : f * f = 1 := by simpa [pow_two] using hF.1.2 f hf
        show p' * f * p'⁻¹ * (p' * f * p'⁻¹) = 1
        calc p' * f * p'⁻¹ * (p' * f * p'⁻¹) = p' * (f * f) * p'⁻¹ := by group
          _ = 1 := by rw [this]; group
      have hsg := sign_eq_one_of_oTwoUpper Φ hAo'
        (show (⟨p' * f * p'⁻¹, hqN⟩ : N) ∈ A.subgroupOf N from hqA)
      exact mem_of_sq_one_of_sign Φ hF4 hF2 hq2 hsg
    have := Subgroup.card_dvd_of_le hPN
    rw [hP16, hNcard] at this
    omega


end CFSG.Quasithin.S151L33

namespace CFSG.Quasithin
open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_autOn {X L : Subgroup G} (hXN : X ≤ Subgroup.normalizer (L : Set G)) {s : G}
    (hsL : s ∈ L) (hsX : s ∈ Subgroup.normalizer (X : Set G)) {a : MulAut ↥L}
    (ha : a ∈ autOn X L) :
    MulAut.conj (⟨s, hsL⟩ : ↥L) * a * (MulAut.conj (⟨s, hsL⟩ : ↥L))⁻¹ ∈ autOn X L := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := (A4.mem_autOn_iff hXN).mp ha
  rw [A4.mem_autOn_iff hXN]
  refine ⟨⟨s * x * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsX x).mp hx⟩, ?_⟩
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  simp only [A4.actionOn_apply_coe, MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply,
    Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conj_symm_apply]
  group


theorem noL33
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hcomp : IsComponentOf L (g1_1516 Z₁)) (hmodel : IsPSL 3 3 1 ↥L) : False := by
  have hLcomp : L ∈ cComp (g1_1516 Z₁) :=
    Id2519.mem_cComp_of_isComponentIn (DoubleA3.isComponentIn_iff_open.mpr hcomp)
  obtain ⟨hN, hV2ne⟩ := hc.h19.seven L hLcomp hc.hL.quasi hc.hL.not_le
  set X : Subgroup G := oTwoUpper (M ⊓ g1_1516 Z₁) with hX
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := le_trans le_sup_left hN
  have hVN : V₂ ≤ Subgroup.normalizer (L : Set G) := le_trans le_sup_right hN
  have hcomm : ⁅V₂, X⁆ = V₂ := hc.ctx.setting.v2_comm
  have hSL : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
  have hSX : s1516 T Z₁ ≤ Subgroup.normalizer (X : Set G) :=
    (hc.h17.sylow.1).trans (by rw [inf_comm]; exact le_normalizer_oTwoUpper (M ⊓ g1_1516 Z₁))
  have hV2e : IsElemAbelian 2 V₂ :=
    isElemAbelian_mono151 hc.ctx.setting.v2_le (isElemAbelian_V154 hc.ctx.qtfe hc.ctx.mf)
  have hfacts : SmallListFacts ↥L := (Unc25L33.l33_facts ↥L hmodel).1
  have hZ : Subgroup.center ↥L = ⊥ := F420.center_eq_bot_of_statedPSL hmodel
  set X' : Subgroup (MulAut ↥L) := autOn X L with hX'
  set V' : Subgroup (MulAut ↥L) := autOn V₂ L with hV'
  have hV'comm : V' = ⁅V', X'⁆ := by
    rw [hV', hX', ← C1Pack5.autOn_commutator hVN hXN, hcomm]
  have hV'e : IsElemAbelian 2 V' := H13.isElemAbelian_autOn hV2e
  have hX'o : oTwoUpper X' = X' := by
    rw [hX', A4.oTwoUpper_autOn hXN, hX, C1Pack153.oTwoUpper_idem']
  have hX'inn : X' ≤ innerAut ↥L := by
    conv_lhs => rw [← hX'o]
    exact oTwoUpper_le_of_pow_mem fun a _ => hfacts.out_two a
  have hinn_normal : (innerAut ↥L).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal ↥L
  have hV'inn : V' ≤ innerAut ↥L := by
    rw [hV'comm]
    exact (Subgroup.commutator_le_right V' (innerAut ↥L)).trans'
      (Subgroup.commutator_mono le_rfl hX'inn)
  have hV'ne : V' ≠ ⊥ := by
    intro hbot
    apply hV2ne
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    have hmem : A4.actionOn L V₂ hVN ⟨v, hv⟩ ∈ V' :=
      (A4.mem_autOn_iff hVN).mpr ⟨⟨v, hv⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (A4.actionOn_eq_one_iff hVN ⟨v, hv⟩).mp hmem
  have hX'V' : X' ≤ Subgroup.normalizer (V' : Set (MulAut ↥L)) := by
    have hle : ⁅X', V'⁆ ≤ V' := by
      rw [Subgroup.commutator_comm]
      exact hV'comm.ge
    have h2 : IsPGroup 2 ↥V' := isPGroup_of_isElemAbelian hV'e
    exact ((isSignalizer_iff_commutator_le (M := ⊤) le_top h2).mpr hle).2.2
  have hinj : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hc : a ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := MulEquiv.ext_iff.1 ha g
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * a = a * g * a⁻¹ * a := by rw [this]
        _ = a * g := by group
    rw [hZ] at hc
    exact hc
  set cL : ↥L →* MulAut ↥L := MulAut.conj with hcL
  set F : Subgroup ↥L := V'.comap cL with hF
  set A : Subgroup ↥L := X'.comap cL with hA
  have hFmap : F.map cL = V' := Subgroup.map_comap_eq_self hV'inn
  have hAmap : A.map cL = X' := Subgroup.map_comap_eq_self hX'inn
  have hmemA : ∀ a : ↥L, a ∈ A ↔ cL a ∈ X' := fun a => Iff.rfl
  have hmemF : ∀ a : ↥L, a ∈ F ↔ cL a ∈ V' := fun a => Iff.rfl
  have hAo : A = oTwoUpper A := by
    apply Subgroup.map_injective hinj
    rw [← oTwoUpper_map, hAmap, hX'o]
  have hAF : A ≤ Subgroup.normalizer (F : Set ↥L) := by
    intro a ha
    refine A4.mem_normalizer_of_conj_mem fun f hf => ?_
    have h1 : cL a ∈ Subgroup.normalizer (V' : Set (MulAut ↥L)) := hX'V' ((hmemA a).mp ha)
    have h2 : cL a * cL f * (cL a)⁻¹ ∈ V' :=
      (Subgroup.mem_normalizer_iff.mp h1 _).mp ((hmemF f).mp hf)
    rw [hmemF, map_mul, map_mul, map_inv]
    exact h2
  have hAc : ¬ A ≤ Subgroup.centralizer (F : Set ↥L) := by
    intro hle
    apply hV'ne
    have hcomm0 : ⁅V', X'⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨f, hf, rfl⟩ : v ∈ F.map cL := hFmap ▸ hv
      obtain ⟨a, ha, rfl⟩ : x ∈ A.map cL := hAmap ▸ hx
      rw [← map_mul, ← map_mul]
      congr 1
      exact (Subgroup.mem_centralizer_iff.mp (hle ha) f hf).symm
    exact hV'comm.trans hcomm0
  have hFe : IsElemAbelian 2 F := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinj
      have h1 := hV'e.1.is_comm.comm ⟨cL a, (hmemF a).mp a.2⟩ ⟨cL b, (hmemF b).mp b.2⟩
      have h2 := congrArg Subtype.val h1
      simpa [map_mul] using h2
    · apply hinj
      have h1 := hV'e.2 (cL x) ((hmemF x).mp hx)
      simpa [map_pow] using h1
  have hrank : twoRank ↥L ≤ 2 :=
    CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_three_three hmodel
  have hFle : Nat.card F ≤ 4 := card_le_four_of_twoRank_le_two hrank hFe
  have hFne : F ≠ ⊥ := by
    intro h
    apply hV'ne
    rw [← hFmap, h, Subgroup.map_bot]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF4 : Nat.card F = 4 := by
    have hF2 : IsPGroup 2 ↥F := isPGroup_of_isElemAbelian hFe
    obtain ⟨k, hk⟩ := hF2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hFne ((Subgroup.card_eq_one).1 (by simpa using hk))
    have hk1 : k ≠ 1 := by
      rintro rfl
      apply hAc
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      by_cases hf1 : f = 1
      · rw [hf1]; simp
      · have hcard : Nat.card F = 2 := by simpa using hk
        obtain ⟨y0, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥F)).1 hcard
        have hconj : a * f * a⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp (hAF ha) f).mp hf
        have h1 : (⟨f, hf⟩ : ↥F) = y0 := huniq _ (fun h => hf1 (congrArg Subtype.val h))
        have h3 : (⟨a * f * a⁻¹, hconj⟩ : ↥F) = y0 := huniq _ (fun h => by
          apply hf1
          have h4 : a * f * a⁻¹ = 1 := congrArg Subtype.val h
          simpa using h4)
        have h5 : a * f * a⁻¹ = f := congrArg Subtype.val (h3.trans h1.symm)
        calc f * a = (a * f * a⁻¹) * a := by rw [h5]
          _ = a * f := by group
    have hk2 : 2 ≤ k := by omega
    have hle : 2 ^ k ≤ 4 := hk ▸ hFle
    have hk2' : k ≤ 2 := by
      by_contra hlt
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : k = 2 := by omega
    rw [hk, this]
    norm_num
  have hFour : IsFourSubgroup F := ⟨hFe, hF4⟩
  have hPA : (s1516 T Z₁ ⊓ L).subgroupOf L ≤ Subgroup.normalizer (A : Set ↥L) := by
    intro s hs
    have hsS : (s : G) ∈ s1516 T Z₁ := (Subgroup.mem_subgroupOf.mp hs).1
    refine A4.mem_normalizer_of_conj_mem fun a ha => ?_
    have h1 := conj_mem_autOn hXN s.2 (hSX hsS) ((hmemA a).mp ha)
    rw [hmemA, map_mul, map_mul, map_inv]
    exact h1
  have hP : IsSylowTwoOf ((s1516 T Z₁ ⊓ L).subgroupOf L) (⊤ : Subgroup ↥L) := by
    refine ⟨le_top, hSL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSL.1).symm, ?_⟩
    rw [show (((s1516 T Z₁ ⊓ L).subgroupOf L).subgroupOf ⊤).index =
      ((s1516 T Z₁ ⊓ L).subgroupOf L).index from Subgroup.relIndex_top_right _]
    exact hSL.2.2
  exact S151L33.ffl hmodel hP hFour hAo hAF hAc hPA


theorem compListNoL33_holds :
    CompListNoL33 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hmodel
  exact noL33 hc hcomp hmodel


end CFSG.Quasithin
