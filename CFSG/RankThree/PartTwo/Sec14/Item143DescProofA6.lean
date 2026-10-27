module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.KFacts.K412AlternatingSix
import CFSG.CGT.Timmesfeld75.A6Basic
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.RankThree.PartTwo.Sec14.Notation
import CFSG.RankThree.PartTwo.KFacts.K412Alternating

public section

namespace CFSG.RankThree.PartTwo.Sec14

namespace Desc143X

namespace A6

open Equiv CFSG.RankThree.PartTwo.KFacts.K412

private def vS (i j : Fin 3) : Perm (Fin 6) :=
  if i = 0 then swap 0 3 * swap 4 5 else if j = 0 then swap 0 1 * swap 2 3
  else if i = j then swap 0 3 * swap 1 4 else swap 0 3 * swap 1 5

private def vT (i j : Fin 3) : Perm (Fin 6) :=
  if i = 0 then swap 0 4 * swap 3 5 else if j = 0 then swap 0 2 * swap 1 3
  else if i = j then swap 1 4 * swap 2 5 else swap 1 5 * swap 2 4

private theorem v_spec : ∀ i j : Fin 3, (i, j) ≠ (0, 0) →
    Perm.sign (vS i j) = 1 ∧ Perm.sign (vT i j) = 1 ∧ vS i j ^ 2 = 1 ∧ vT i j ^ 2 = 1 ∧
    vS i j ≠ 1 ∧ vT i j ≠ 1 ∧ vS i j ≠ vT i j ∧ vS i j * vT i j = vT i j * vS i j ∧
    (sixF i j * vS i j * (sixF i j)⁻¹ = vS i j ∨ sixF i j * vS i j * (sixF i j)⁻¹ = vT i j ∨
      sixF i j * vS i j * (sixF i j)⁻¹ = vS i j * vT i j) ∧
    (sixF i j * vT i j * (sixF i j)⁻¹ = vS i j ∨ sixF i j * vT i j * (sixF i j)⁻¹ = vT i j ∨
      sixF i j * vT i j * (sixF i j)⁻¹ = vS i j * vT i j) := by
  decide +kernel

private theorem card_filter_comm : ∀ i j : Fin 3, (i, j) ≠ (0, 0) →
    (Finset.univ.filter (fun y : Perm (Fin 6) => y ^ 2 = 1 ∧ y ≠ 1 ∧
      y * sixF i j = sixF i j * y ∧ Perm.sign y = 1)).card = 0 := by
  decide +kernel

private theorem card_filter_nine :
    (Finset.univ.filter (fun y : Perm (Fin 6) => y ^ 9 = 1 ∧ y ^ 3 ≠ 1)).card = 0 := by
  decide +kernel

private theorem exists_conj_sixF {x : Perm (Fin 6)} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ (h : Perm (Fin 6)) (i j : Fin 3), (i, j) ≠ (0, 0) ∧ x = h * sixF i j * h⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE0 : IsPGroup 3 eSix := IsPGroup.of_card (n := 2) (by rw [card_eSix]; norm_num)
  have hx : IsPGroup 3 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1, pow_one])
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hx (hE0.toSylow (not_three_dvd_index_six card_eSix))
  have hmem : g * x * g⁻¹ ∈ eSix := hg ⟨x, Subgroup.mem_zpowers x, rfl⟩
  obtain ⟨i, j, hij⟩ := hmem
  refine ⟨g⁻¹, i, j, fun h => hx1 ?_, ?_⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rw [sixF_zero] at hij
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [hij]; group
  · rw [← hij]
    group

variable {X : Type*} [Group X]

private def emb (φ : X ≃* alternatingGroup (Fin 6)) : X →* Perm (Fin 6) :=
  (alternatingGroup (Fin 6)).subtype.comp φ.toMonoidHom

private theorem emb_injective (φ : X ≃* alternatingGroup (Fin 6)) :
    Function.Injective (emb φ) :=
  Subtype.val_injective.comp φ.injective

private theorem sign_emb (φ : X ≃* alternatingGroup (Fin 6)) (x : X) :
    Perm.sign (emb φ x) = 1 :=
  Perm.mem_alternatingGroup.mp (φ x).2

private theorem sign_conj (g y : Perm (Fin 6)) : Perm.sign (g * y * g⁻¹) = Perm.sign y := by
  rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, mul_comm (Perm.sign g), mul_assoc,
    Int.units_mul_self, mul_one]

private theorem exists_conj_emb (φ : X ≃* alternatingGroup (Fin 6)) {x : X} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) :
    ∃ (h : Perm (Fin 6)) (i j : Fin 3), (i, j) ≠ (0, 0) ∧ emb φ x = h * sixF i j * h⁻¹ :=
  exists_conj_sixF (by rw [← map_pow, hx3, map_one])
    (fun h => hx1 (emb_injective φ (h.trans (map_one (emb φ)).symm)))

theorem mul_ne_of_three_two (φ : X ≃* alternatingGroup (Fin 6)) {x y : X} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) : x * y ≠ y * x := by
  intro hxy
  obtain ⟨h, i, j, hij, hx⟩ := exists_conj_emb φ hx3 hx1
  have hmem : h⁻¹ * emb φ y * h⁻¹⁻¹ ∈ Finset.univ.filter (fun y : Perm (Fin 6) => y ^ 2 = 1 ∧
      y ≠ 1 ∧ y * sixF i j = sixF i j * y ∧ Perm.sign y = 1) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_, ?_⟩
    · rw [conj_pow, ← map_pow, hy2, map_one, mul_one, mul_inv_cancel]
    · intro h1
      apply hy1
      apply emb_injective φ
      rw [map_one]
      calc emb φ y = h * (h⁻¹ * emb φ y * h⁻¹⁻¹) * h⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · have e1 : sixF i j = h⁻¹ * emb φ x * h⁻¹⁻¹ := by rw [hx]; group
      rw [e1]
      calc h⁻¹ * emb φ y * h⁻¹⁻¹ * (h⁻¹ * emb φ x * h⁻¹⁻¹) = h⁻¹ * emb φ (y * x) * h⁻¹⁻¹ := by
            rw [map_mul]; group
        _ = h⁻¹ * emb φ (x * y) * h⁻¹⁻¹ := by rw [hxy]
        _ = h⁻¹ * emb φ x * h⁻¹⁻¹ * (h⁻¹ * emb φ y * h⁻¹⁻¹) := by rw [map_mul]; group
    · rw [sign_conj, sign_emb]
  rw [Finset.card_eq_zero.mp (card_filter_comm i j hij)] at hmem
  simp at hmem

theorem pow_three_of_pow_nine (φ : X ≃* alternatingGroup (Fin 6)) {x : X} (h9 : x ^ 9 = 1) :
    x ^ 3 = 1 := by
  by_contra h3
  have hmem : emb φ x ∈
      Finset.univ.filter (fun y : Perm (Fin 6) => y ^ 9 = 1 ∧ y ^ 3 ≠ 1) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, by rw [← map_pow, h9, map_one], fun h => h3 ?_⟩
    apply emb_injective φ
    rw [map_pow, h, map_one]
  rw [Finset.card_eq_zero.mp card_filter_nine] at hmem
  simp at hmem

theorem exists_klein (φ : X ≃* alternatingGroup (Fin 6)) {x : X} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) :
    ∃ s t : X, s ^ 2 = 1 ∧ t ^ 2 = 1 ∧ s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t ∧ s * t = t * s ∧
      (x * s * x⁻¹ = s ∨ x * s * x⁻¹ = t ∨ x * s * x⁻¹ = s * t) ∧
      (x * t * x⁻¹ = s ∨ x * t * x⁻¹ = t ∨ x * t * x⁻¹ = s * t) := by
  obtain ⟨h, i, j, hij, hx⟩ := exists_conj_emb φ hx3 hx1
  obtain ⟨hsS, hsT, hS2, hT2, hS1, hT1, hST, hSTc, hxS, hxT⟩ := v_spec i j hij
  set c := MulAut.conj h with hc
  have hmemS : c (vS i j) ∈ alternatingGroup (Fin 6) := by
    rw [Perm.mem_alternatingGroup, hc, MulAut.conj_apply, sign_conj, hsS]
  have hmemT : c (vT i j) ∈ alternatingGroup (Fin 6) := by
    rw [Perm.mem_alternatingGroup, hc, MulAut.conj_apply, sign_conj, hsT]
  set s := φ.symm ⟨c (vS i j), hmemS⟩ with hs
  set t := φ.symm ⟨c (vT i j), hmemT⟩ with ht
  have hψs : emb φ s = c (vS i j) := by simp [emb, s]
  have hψt : emb φ t = c (vT i j) := by simp [emb, t]
  have hψx : emb φ x = c (sixF i j) := by rw [hx, hc, MulAut.conj_apply]
  have key : ∀ {u v : X}, emb φ u = emb φ v → u = v := fun h1 => emb_injective φ h1
  refine ⟨s, t, key ?_, key ?_, fun h1 => hS1 ?_, fun h1 => hT1 ?_, fun h1 => hST ?_, key ?_, ?_,
    ?_⟩
  · rw [map_pow, hψs, ← map_pow, hS2, map_one, map_one]
  · rw [map_pow, hψt, ← map_pow, hT2, map_one, map_one]
  · apply c.injective
    rw [← hψs, h1, map_one, map_one]
  · apply c.injective
    rw [← hψt, h1, map_one, map_one]
  · apply c.injective
    rw [← hψs, ← hψt, h1]
  · rw [map_mul, map_mul, hψs, hψt, ← map_mul, ← map_mul, hSTc]
  · have e : emb φ (x * s * x⁻¹) = c (sixF i j * vS i j * (sixF i j)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hψx, hψs, ← map_inv, ← map_mul, ← map_mul]
    rcases hxS with h1 | h1 | h1
    · exact Or.inl (key (by rw [e, h1, hψs]))
    · exact Or.inr (Or.inl (key (by rw [e, h1, hψt])))
    · exact Or.inr (Or.inr (key (by rw [e, h1, map_mul, map_mul, hψs, hψt])))
  · have e : emb φ (x * t * x⁻¹) = c (sixF i j * vT i j * (sixF i j)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hψx, hψt, ← map_inv, ← map_mul, ← map_mul]
    rcases hxT with h1 | h1 | h1
    · exact Or.inl (key (by rw [e, h1, hψs]))
    · exact Or.inr (Or.inl (key (by rw [e, h1, hψt])))
    · exact Or.inr (Or.inr (key (by rw [e, h1, map_mul, map_mul, hψs, hψt])))

variable [Finite X]

omit [Finite X] in
theorem card_eq (φ : X ≃* alternatingGroup (Fin 6)) : Nat.card X = 360 := by
  rw [Nat.card_congr φ.toEquiv, CFSG.CGT.Timmesfeld75.card_alternatingGroup_six]

omit [Finite X] in
theorem isSimpleGroup (φ : X ≃* alternatingGroup (Fin 6)) : IsSimpleGroup X :=
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  MulEquiv.isSimpleGroup φ

theorem eq_top_of_index_le_five (φ : X ≃* alternatingGroup (Fin 6)) {H : Subgroup X}
    (hH : H.index ≤ 5) : H = ⊤ := by
  have := isSimpleGroup φ
  rcases (Subgroup.normalCore_normal H).eq_bot_or_eq_top with hb | ht
  · exfalso
    have hinj : Function.Injective (MulAction.toPermHom X (X ⧸ H)) := by
      rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hb]
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm, card_eq φ] at h1
    have h2 : (Nat.card (X ⧸ H)).factorial ≤ 120 :=
      (Nat.factorial_le (show Nat.card (X ⧸ H) ≤ 5 from hH)).trans (by decide)
    omega
  · exact eq_top_iff.mpr (ht ▸ Subgroup.normalCore_le H)

omit [Finite X] in
theorem card_sup_eq_four [Finite X] {s t : X} (hs2 : s ^ 2 = 1) (ht2 : t ^ 2 = 1) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s ≠ t) (hcomm : s * t = t * s) :
    Nat.card (Subgroup.zpowers s ⊔ Subgroup.zpowers t : Subgroup X) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hos : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  have hot : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have htn : t ∉ Subgroup.zpowers s := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← zpow_mod_orderOf, hos] at hk
    have : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases this with h0 | h1
    · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero] at hk
      exact ht1 hk.symm
    · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one] at hk
      exact hst hk
  have hdisj : Subgroup.zpowers s ⊓ Subgroup.zpowers t = ⊥ :=
    Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_two hot htn
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers s)
    (Subgroup.zpowers t) fun x hx y hy => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_zpow hcomm m n).eq
  rwa [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hos, hot] at hcard

private theorem false_of_card_eq_36 (φ : X ≃* alternatingGroup (Fin 6)) {H : Subgroup X}
    (h36 : Nat.card H = 36) {s t : X} (hsH : s ∈ H) (htH : t ∈ H) (hs2 : s ^ 2 = 1)
    (ht2 : t ^ 2 = 1) (hs1 : s ≠ 1) (ht1 : t ≠ 1) (hst : s ≠ t) (hcomm : s * t = t * s) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have K2 : ∀ x y : H, x ^ 3 = 1 → x ≠ 1 → y ^ 2 = 1 → y ≠ 1 → x * y ≠ y * x := by
    intro x y hx3 hx1 hy2 hy1 hxy
    exact mul_ne_of_three_two φ (x := (x : X)) (y := (y : X))
      (by simpa using congrArg Subtype.val hx3) (fun h => hx1 (Subtype.ext h))
      (by simpa using congrArg Subtype.val hy2) (fun h => hy1 (Subtype.ext h))
      (by simpa using congrArg Subtype.val hxy)
  have K4 : ∀ x : H, x ^ 9 = 1 → x ^ 3 = 1 := fun x h9 => Subtype.ext (by
    simpa using pow_three_of_pow_nine φ (x := (x : X)) (by simpa using congrArg Subtype.val h9))
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2) (G := H)
    (by rw [h36]; norm_num)
  have hPab : ∀ a b : P, a * b = b * a := fun a b =>
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq hP).is_comm.comm a b
  have hP3 : ∀ p ∈ P, p ^ 3 = 1 := by
    intro p hp
    refine K4 p ?_
    have h1 : (⟨p, hp⟩ : P) ^ Nat.card P = 1 := pow_card_eq_one'
    rw [hP] at h1
    simpa using congrArg Subtype.val h1
  have hPne : ∃ p ∈ P, p ≠ 1 := by
    by_contra hall
    push Not at hall
    have : P = ⊥ := (Subgroup.eq_bot_iff_forall P).mpr hall
    rw [this, Subgroup.card_bot] at hP
    norm_num at hP
  obtain ⟨p₀, hp₀, hp₀1⟩ := hPne
  set s' : H := ⟨s, hsH⟩ with hs'
  set t' : H := ⟨t, htH⟩ with ht'
  have hs'2 : s' ^ 2 = 1 := Subtype.ext (by simpa using hs2)
  have ht'2 : t' ^ 2 = 1 := Subtype.ext (by simpa using ht2)
  have hs'1 : s' ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  by_cases hn : P.Normal
  ·
    have hinv : ∀ u : H, u ^ 2 = 1 → u ≠ 1 → ∀ p ∈ P, u * p * u⁻¹ = p⁻¹ := by
      intro u hu2 hu1 p hp
      have hu' : u⁻¹ = u := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two, hu2]
      have hup : u * p * u⁻¹ ∈ P := hn.conj_mem p hp u
      set q := p * (u * p * u⁻¹) with hq
      have hqP : q ∈ P := P.mul_mem hp hup
      have hpc : (u * p * u⁻¹) * p = p * (u * p * u⁻¹) :=
        congrArg Subtype.val (hPab ⟨_, hup⟩ ⟨p, hp⟩)
      have hu'' : u * u = 1 := by rw [← pow_two, hu2]
      have hqu : q * u = u * q := by
        have e1 : u * q * u⁻¹ = (u * p * u⁻¹) * p := by
          rw [hq, hu']
          simp only [mul_assoc, hu'', mul_one]
        rw [hpc] at e1
        calc q * u = u * q * u⁻¹ * u := by rw [e1, hq]
          _ = u * q := by group
      by_contra hne
      have hq1 : q ≠ 1 := fun h1 => hne (eq_inv_of_mul_eq_one_right h1)
      exact K2 q u (hP3 q hqP) hq1 hu2 hu1 hqu
    have hst2 : (s' * t') ^ 2 = 1 := by
      have hc' : s' * t' = t' * s' := Subtype.ext (by simpa using hcomm)
      rw [pow_two, show s' * t' * (s' * t') = s' * (t' * s') * t' by group, ← hc',
        show s' * (s' * t') * t' = (s' * s') * (t' * t') by group, ← pow_two, ← pow_two, hs'2,
        ht'2, one_mul]
    have hst1 : s' * t' ≠ 1 := by
      intro h1
      apply hst
      have : t' = s'⁻¹ := (eq_inv_of_mul_eq_one_right h1)
      have hsi : s'⁻¹ = s' := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hs'2]
      rw [hsi] at this
      exact (congrArg Subtype.val this).symm
    apply K2 p₀ (s' * t') (hP3 p₀ hp₀) hp₀1 hst2 hst1
    have e : (s' * t') * p₀ * (s' * t')⁻¹ = p₀ := by
      calc (s' * t') * p₀ * (s' * t')⁻¹ = s' * (t' * p₀ * t'⁻¹) * s'⁻¹ := by group
        _ = s' * p₀⁻¹ * s'⁻¹ := by rw [hinv t' ht'2 ht'1 p₀ hp₀]
        _ = (s' * p₀ * s'⁻¹)⁻¹ := by group
        _ = p₀ := by rw [hinv s' hs'2 hs'1 p₀ hp₀, inv_inv]
    calc p₀ * (s' * t') = (s' * t') * p₀ * (s' * t')⁻¹ * (s' * t') := by rw [e]
      _ = (s' * t') * p₀ := by group
  ·
    have hPp : IsPGroup 3 P := IsPGroup.of_card hP
    have hidx : P.index = 4 := by
      have := P.card_mul_index
      rw [hP, h36] at this
      omega
    set S : Sylow 3 H := hPp.toSylow (by rw [hidx]; norm_num) with hS
    have hSP : (S : Subgroup H) = P := rfl
    have hn3 : Nat.card (Sylow 3 H) ≠ 1 := by
      intro h1
      have : Subsingleton (Sylow 3 H) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hn (hSP ▸ Sylow.normal_of_subsingleton S)
    have hmod := card_sylow_modEq_one 3 H
    have hdvd := Sylow.card_dvd_index S
    rw [hSP, hidx] at hdvd
    have h4 : Nat.card (Sylow 3 H) = 4 := by
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : Nat.card (Sylow 3 H)
      · simp at hdvd
      · exact absurd rfl hn3
      · exact absurd hmod (by decide)
      · exact absurd hdvd (by decide)
      · rfl
    have hNi : (Subgroup.normalizer (P : Set H)).index = 4 := by
      rw [← h4, Sylow.card_eq_index_normalizer S]
      rfl
    have hNcard : Nat.card (Subgroup.normalizer (P : Set H)) = 9 := by
      have := (Subgroup.normalizer (P : Set H)).card_mul_index
      rw [hNi, h36] at this
      omega
    have hNP : Subgroup.normalizer (P : Set H) = P :=
      (Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer (by rw [hNcard, hP]; norm_num)).symm
    have hNC : Subgroup.normalizer (S : Set H) ≤ Subgroup.centralizer (S : Set H) := by
      show Subgroup.normalizer (P : Set H) ≤ Subgroup.centralizer (P : Set H)
      rw [hNP]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hPab ⟨y, hy⟩ ⟨x, hx⟩)
    set K := (MonoidHom.transferSylow S hNC).ker with hK
    have hKc : K.IsComplement' (S : Subgroup H) := MonoidHom.ker_transferSylow_isComplement' S hNC
    have hKcard : Nat.card K = 4 := by
      have := hKc.card_mul_card
      have hS9 : Nat.card (S : Subgroup H) = 9 := hP
      rw [hS9, h36] at this
      omega
    have hKn : K.Normal := MonoidHom.normal_ker _
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (by rw [hKcard]; norm_num)
    set ρ : P →* Equiv.Perm K :=
      (MulAut.toPerm ↥K).comp ((MulAut.conjNormal (H := K)).comp P.subtype) with hρ
    have hninj : ¬ Function.Injective ρ := by
      intro hinj
      have h1 := Subgroup.card_dvd_of_injective ρ hinj
      rw [hP, Nat.card_perm, hKcard] at h1
      norm_num [Nat.factorial] at h1
    rw [← MonoidHom.ker_eq_bot_iff] at hninj
    obtain ⟨⟨q, hqker⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hninj
    obtain ⟨p, hpP⟩ := q
    have hp1 : (⟨p, hpP⟩ : P) ≠ 1 := fun h => hq1 (Subtype.ext h)
    have hpker : (⟨p, hpP⟩ : P) ∈ ρ.ker := hqker
    have hp1' : p ≠ 1 := fun h => hp1 (Subtype.ext h)
    have hpk : p * (k : H) = (k : H) * p := by
      have h1 : ρ ⟨p, hpP⟩ k = k := by rw [MonoidHom.mem_ker.mp hpker]; rfl
      have h2 : ((MulAut.conjNormal (H := K) p) k : H) = p * k * p⁻¹ :=
        MulAut.conjNormal_apply p k
      have h3 : ((MulAut.conjNormal (H := K) p) k : H) = (k : H) := congrArg Subtype.val h1
      rw [h2] at h3
      calc p * (k : H) = p * k * p⁻¹ * p := by group
        _ = (k : H) * p := by rw [h3]
    have hk2 : (k : H) ^ 2 = 1 := by
      have := pow_orderOf_eq_one k
      rw [hk] at this
      simpa using congrArg Subtype.val this
    have hk1 : (k : H) ≠ 1 := by
      intro h1
      have : k = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hk
      norm_num at hk
    exact K2 p k (hP3 p hpP) hp1' hk2 hk1 hpk

theorem eq_top_of_le (φ : X ≃* alternatingGroup (Fin 6)) {H : Subgroup X} (h9 : 9 ∣ Nat.card H)
    {s t : X} (hsH : s ∈ H) (htH : t ∈ H) (hs2 : s ^ 2 = 1) (ht2 : t ^ 2 = 1) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s ≠ t) (hcomm : s * t = t * s) : H = ⊤ := by
  have hX := card_eq φ
  have h4 : 4 ∣ Nat.card H := by
    rw [← card_sup_eq_four hs2 ht2 hs1 ht1 hst hcomm]
    exact Subgroup.card_dvd_of_le
      (sup_le (Subgroup.zpowers_le.mpr hsH) (Subgroup.zpowers_le.mpr htH))
  have h36 : 36 ∣ Nat.card H := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h9 h4
  have hmul := H.card_mul_index
  rw [hX] at hmul
  by_cases hi : H.index ≤ 5
  · exact eq_top_of_index_le_five φ hi
  exfalso
  obtain ⟨k, hk⟩ := h36
  rw [hk] at hmul
  have hki : k * H.index = 10 := by
    have : 36 * (k * H.index) = 36 * 10 := by rw [← mul_assoc]; omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hidx : H.index ∣ 10 := ⟨k, by rw [← hki, mul_comm]⟩
  have hle := Nat.le_of_dvd (by norm_num) hidx
  have hi10 : H.index = 10 := by
    interval_cases h : H.index <;> omega
  rw [hi10] at hki
  have hk1 : k = 1 := by omega
  rw [hk1] at hk
  exact false_of_card_eq_36 φ hk hsH htH hs2 ht2 hs1 ht1 hst hcomm

omit [Finite X] in
private theorem mem_normalizer_map_conj {M : Subgroup X} {g p : X}
    (hg : p⁻¹ * g * p ∈ Subgroup.normalizer (M : Set X)) :
    g ∈ Subgroup.normalizer ((M.map (MulAut.conj p).toMonoidHom : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro y
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨p⁻¹ * g * p * m * (p⁻¹ * g * p)⁻¹, (hg m).mp hm, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨m, hm, hmy⟩
    refine ⟨(p⁻¹ * g * p)⁻¹ * m * (p⁻¹ * g * p), ?_, ?_⟩
    · have := (hg ((p⁻¹ * g * p)⁻¹ * m * (p⁻¹ * g * p))).mpr (by
        rw [show p⁻¹ * g * p * ((p⁻¹ * g * p)⁻¹ * m * (p⁻¹ * g * p)) * (p⁻¹ * g * p)⁻¹ = m by
          group]
        exact hm)
      exact this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmy ⊢
      calc p * ((p⁻¹ * g * p)⁻¹ * m * (p⁻¹ * g * p)) * p⁻¹ = g⁻¹ * (p * m * p⁻¹) * g := by group
        _ = y := by rw [hmy]; group

theorem sSup_eq_top (hq : CFSG.IsQuasisimple X)
    (htc : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) {E : Subgroup X}
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE9 : Nat.card E = 9) (hZE : Subgroup.center X ≤ E) :
    sSup {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ E ≤ Subgroup.normalizer (Y : Set X)} = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZ3, ⟨ψ⟩⟩ := htc
  set Z := Subgroup.center X with hZ
  set π := QuotientGroup.mk' Z with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : ∀ r, π r = 1 ↔ r ∈ Z := fun r => QuotientGroup.eq_one_iff r
  have hZpow : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => by
    have h1 : (⟨z, hz⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
    rw [hZ3] at h1
    simpa using congrArg Subtype.val h1
  have hZc : ∀ z ∈ Z, ∀ r : X, z * r = r * z := fun z hz r =>
    (Subgroup.mem_center_iff.mp hz r).symm
  obtain ⟨x, hxE, hxZ⟩ : ∃ x ∈ E, x ∉ Z := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show E ≤ Z from hall)
    rw [hE9, hZ3] at h1
    norm_num at h1
  have hx3 : x ^ 3 = 1 := hE3 x hxE
  have hπx1 : π x ≠ 1 := fun h => hxZ ((hker x).mp h)
  have hπx3 : π x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 (fun h => hxZ (h ▸ Z.one_mem))
  obtain ⟨hcardZx, hsetZx⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Z
    (Subgroup.zpowers x) fun z hz y _ => hZc z hz y
  have hdisj : Z ⊓ Subgroup.zpowers x = ⊥ :=
    Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hox hxZ
  rw [hdisj, Subgroup.card_bot, mul_one, hZ3, Nat.card_zpowers, hox] at hcardZx
  have hEeq : E = Z ⊔ Subgroup.zpowers x :=
    (Subgroup.eq_of_le_of_card_ge (sup_le hZE (Subgroup.zpowers_le.mpr hxE))
      (by rw [hE9, hcardZx])).symm
  have hπE : ∀ e ∈ E, π e ∈ Subgroup.zpowers (π x) := by
    intro e he
    have he' : e ∈ ((Z ⊔ Subgroup.zpowers x : Subgroup X) : Set X) := hEeq ▸ he
    rw [hsetZx] at he'
    obtain ⟨z, hz, y, hy, rfl⟩ := Set.mem_mul.mp he'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [map_mul, (hker z).mpr hz, one_mul, map_zpow]
  obtain ⟨s₁, t₁, hs₁2, ht₁2, hs₁1, ht₁1, hst₁, hc₁, hxs, hxt⟩ := exists_klein ψ hπx3 hπx1
  set W₁ := Subgroup.zpowers s₁ ⊔ Subgroup.zpowers t₁ with hW₁
  have hcW : ∀ u, (u = s₁ ∨ u = t₁ ∨ u = s₁ * t₁) → u ∈ W₁ := by
    rintro u (rfl | rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact W₁.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hmapW : W₁.map (MulAut.conj (π x)).toMonoidHom ≤ W₁ := by
    rw [hW₁, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le (Subgroup.zpowers_le.mpr (hcW _ hxs)) (Subgroup.zpowers_le.mpr (hcW _ hxt))
  have hxW : π x ∈ Subgroup.normalizer (W₁ : Set (X ⧸ Z)) :=
    Subgroup.mem_normalizer_fintype fun w hw => hmapW ⟨w, hw, rfl⟩
  set V := W₁.comap π with hV
  have hEV : E ≤ Subgroup.normalizer (V : Set X) := by
    intro e he
    have hπe : π e ∈ Subgroup.normalizer (W₁ : Set (X ⧸ Z)) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hπE e he)
      rw [← hk]
      exact zpow_mem hxW k
    rw [Subgroup.mem_normalizer_iff] at hπe ⊢
    intro r
    rw [hV, Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hπe (π r)
  set Y := CFSG.GH74.GLS.pPrimeCoreOf 3 V with hY
  have hY3 : ¬ 3 ∣ Nat.card Y := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (Sec14.coprime_card_pPrimeCoreOf 3 V)
  have hEY : E ≤ Subgroup.normalizer (Y : Set X) :=
    hEV.trans (Sec14.normalizer_le_normalizer_pPrimeCoreOf 3 V)
  have lift : ∀ u : X ⧸ Z, u ^ 2 = 1 → ∃ v : X, π v = u ∧ v ^ 2 = 1 := by
    intro u hu
    obtain ⟨w, rfl⟩ := hπs u
    refine ⟨w ^ 3, ?_, ?_⟩
    · rw [map_pow, pow_succ, hu, one_mul]
    · have hw2 : w ^ 2 ∈ Z := (hker _).mp (by rw [map_pow, hu])
      rw [← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul]
      exact hZpow _ hw2
  obtain ⟨s, hπs', hs2⟩ := lift s₁ hs₁2
  obtain ⟨t, hπt', ht2⟩ := lift t₁ ht₁2
  have hs1 : s ≠ 1 := fun h => hs₁1 (by rw [← hπs', h, map_one])
  have ht1 : t ≠ 1 := fun h => ht₁1 (by rw [← hπt', h, map_one])
  have hst : s ≠ t := fun h => hst₁ (by rw [← hπs', ← hπt', h])
  have hsZ : s ∉ Z := fun h => hs₁1 (by rw [← hπs', (hker s).mpr h])
  have hcomm : s * t = t * s := by
    set z := s * t * s⁻¹ * t⁻¹ with hzdef
    clear_value z
    have hzZ : z ∈ Z := (hker z).mp (by
      rw [hzdef, map_mul, map_mul, map_mul, map_inv, map_inv, hπs', hπt', hc₁]
      group)
    have hss : s * s = 1 := by rw [← pow_two, hs2]
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have h1 : s * t * s⁻¹ = z * t := by rw [hzdef]; group
    have hsz : s * z = z * s := (hZc z hzZ s).symm
    have h2 : t = z * z * t := by
      calc t = (s * s) * t * (s * s)⁻¹ := by rw [hss]; group
        _ = s * (s * t * s⁻¹) * s⁻¹ := by group
        _ = s * (z * t) * s⁻¹ := by rw [h1]
        _ = s * z * t * s⁻¹ := by rw [← mul_assoc]
        _ = z * s * t * s⁻¹ := by rw [hsz]
        _ = z * (s * t * s⁻¹) := by group
        _ = z * z * t := by rw [h1, mul_assoc]
    have hz2 : z * z = 1 := by
      have h3 : z * z * t = 1 * t := by rw [one_mul]; exact h2.symm
      exact mul_right_cancel h3
    have hz1 : z = 1 := by
      have h3 := hZpow z hzZ
      calc z = z ^ 3 * (z * z)⁻¹ := by group
        _ = 1 := by rw [h3, hz2]; group
    calc s * t = z * (t * s) := by rw [hzdef]; group
      _ = t * s := by rw [hz1, one_mul]
  set W := Subgroup.zpowers s ⊔ Subgroup.zpowers t with hW
  have hW4 : Nat.card W = 4 := card_sup_eq_four hs2 ht2 hs1 ht1 hst hcomm
  have hWV : W ≤ V := sup_le
    (Subgroup.zpowers_le.mpr (by rw [hV, Subgroup.mem_comap, hπs']; exact hcW _ (Or.inl rfl)))
    (Subgroup.zpowers_le.mpr (by
      rw [hV, Subgroup.mem_comap, hπt']
      exact hcW _ (Or.inr (Or.inl rfl))))
  have hWmap : W.map π = W₁ := by
    rw [hW, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hπs', hπt']
  have hVW : V ≤ Subgroup.normalizer (W : Set X) := by
    intro v hv
    have hv' : π v ∈ W.map π := hWmap ▸ hv
    obtain ⟨w, hw, hwv⟩ := hv'
    have hz : w⁻¹ * v ∈ Z := (hker _).mp (by rw [map_mul, map_inv, hwv, inv_mul_cancel])
    have hvwz : v = w * (w⁻¹ * v) := by group
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hvwz]
    have e : w * (w⁻¹ * v) * y * (w * (w⁻¹ * v))⁻¹ = w * y * w⁻¹ := by
      have hc := hZc _ hz y
      calc w * (w⁻¹ * v) * y * (w * (w⁻¹ * v))⁻¹ = w * ((w⁻¹ * v) * y) * (w⁻¹ * v)⁻¹ * w⁻¹ := by
            group
        _ = w * (y * (w⁻¹ * v)) * (w⁻¹ * v)⁻¹ * w⁻¹ := by rw [hc]
        _ = w * y * w⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hw) y)
  have hWY : W ≤ Y := Sec14.le_pPrimeCoreOf hWV hVW (by rw [hW4]; norm_num)
  set 𝒴 := {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ E ≤ Subgroup.normalizer (Y : Set X)} with h𝒴
  set T := sSup 𝒴 with hT
  have hYT : Y ≤ T := le_sSup ⟨hY3, hEY⟩
  have hsT : s ∈ T := hYT (hWY (Subgroup.mem_sup_left (Subgroup.mem_zpowers s)))
  have htT : t ∈ T := hYT (hWY (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  have hX : Nat.card X = 1080 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    rw [Nat.card_congr ψ.toEquiv, CFSG.CGT.Timmesfeld75.card_alternatingGroup_six, hZ3] at h1
    omega
  have hP27 : Nat.card (P : Subgroup X) = 27 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have hmul := (P : Subgroup X).card_mul_index
    rw [hk, hX] at hmul
    have hnd := P.not_dvd_index
    have hk6 : k ≤ 6 := by
      by_contra h
      have : 3 ^ 7 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 3 ^ k ≤ 1080 := Nat.le_of_dvd (by norm_num) ⟨_, hmul.symm⟩
      omega
    rw [hk]
    interval_cases k <;> omega
  have hEn : (E.subgroupOf P).Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    have h1 := (E.subgroupOf P).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hE9, hP27] at h1
    rw [hP27, show Nat.minFac 27 = 3 by norm_num]
    omega
  have hPE : (P : Subgroup X) ≤ Subgroup.normalizer (E : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).mp hEn
  have hPT : (P : Subgroup X) ≤ Subgroup.normalizer (T : Set X) := by
    intro p hp
    have hle : T ≤ T.comap (MulAut.conj p).toMonoidHom := by
      refine sSup_le fun M hM m hm => ?_
      have hM' : M.map (MulAut.conj p).toMonoidHom ∈ 𝒴 := by
        refine ⟨?_, fun e he => ?_⟩
        · rw [Subgroup.card_map_of_injective (MulAut.conj p).injective]
          exact hM.1
        · refine mem_normalizer_map_conj (hM.2 ?_)
          have := (Subgroup.mem_normalizer_iff.mp (hPE (inv_mem hp)) e).mp he
          simpa using this
      exact le_sSup hM' ⟨m, hm, rfl⟩
    exact Subgroup.mem_normalizer_fintype fun y hy => hle hy
  have hZP : Z ≤ (P : Subgroup X) := hZE.trans hEP
  have hPmap : Nat.card ((P : Subgroup X).map π) = 9 := by
    have h1 := Subgroup.relIndex_ker (P : Subgroup X) π
    rw [QuotientGroup.ker_mk'] at h1
    have h2 := (Z.subgroupOf (P : Subgroup X)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZ3, hP27] at h2
    rw [← h1]
    show (Z.subgroupOf (P : Subgroup X)).index = 9
    omega
  have hTP : T ⊔ (P : Subgroup X) = ⊤ := by
    have h9 : 9 ∣ Nat.card ((T ⊔ (P : Subgroup X)).map π) := by
      rw [← hPmap]
      exact Subgroup.card_dvd_of_le (Subgroup.map_mono le_sup_right)
    have htop := eq_top_of_le ψ h9 (s := s₁) (t := t₁)
      (hπs' ▸ Subgroup.mem_map_of_mem π (Subgroup.mem_sup_left hsT))
      (hπt' ▸ Subgroup.mem_map_of_mem π (Subgroup.mem_sup_left htT)) hs₁2 ht₁2 hs₁1 ht₁1 hst₁ hc₁
    have h1 := congrArg (Subgroup.comap π) htop
    rw [Subgroup.comap_map_eq, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
    rw [← h1]
    exact (sup_eq_left.mpr (hZP.trans le_sup_right)).symm
  have hTn : T.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hTP]
    exact sup_le Subgroup.le_normalizer hPT
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hTn with h | h
  · exact h
  · exact absurd (h hsT) hsZ

end A6

end Desc143X

end CFSG.RankThree.PartTwo.Sec14
