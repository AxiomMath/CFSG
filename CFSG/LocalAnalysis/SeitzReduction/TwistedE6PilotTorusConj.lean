module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviAutTorus
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPositionBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section SL2

variable {k : Type*} [Field k]

theorem eq_one_of_val_eq_val_inv [CharP k 2] {l : kˣ} (h : (l : k) = ((l⁻¹ : kˣ) : k)) :
    l = 1 := by
  have h1 : (l : k) * l = 1 := by
    calc (l : k) * l = l * ((l⁻¹ : kˣ) : k) := by rw [← h]
      _ = 1 := Units.mul_inv l
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hsq : ((l : k) - 1) * ((l : k) - 1) = 0 := by linear_combination h1 + (1 - (l : k)) * h2
  exact Units.ext (sub_eq_zero.1 (mul_self_eq_zero.1 hsq))

theorem odd_card_sub_one_of_charP_two [Finite k] [CharP k 2] : Odd (Nat.card k - 1) := by
  have := Fintype.ofFinite k
  have h0 : ((Nat.card k : ℕ) : k) = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero k
  obtain ⟨m, hm⟩ := (CharP.cast_eq_zero_iff k 2 _).1 h0
  have h1 : 1 < Nat.card k := Finite.one_lt_card
  exact ⟨m - 1, by omega⟩

theorem exists_conj_eq_HSL_of_ne_one [Finite k] [CharP k 2] {x : SL2 k}
    (hx : x ^ (Nat.card k - 1) = 1) (hx1 : x ≠ 1) :
    ∃ (P : SL2 k) (l : kˣ), P⁻¹ * x * P = HSL l ∧ (l : k) ≠ ((l⁻¹ : kˣ) : k) := by
  have hx2 : x ^ 2 ≠ 1 := by
    intro h
    have hd : orderOf x ∣ Nat.gcd 2 (Nat.card k - 1) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h) (orderOf_dvd_of_pow_eq_one hx)
    rw [Nat.coprime_two_left.2 odd_card_sub_one_of_charP_two, Nat.dvd_one,
      orderOf_eq_one_iff] at hd
    exact hx1 hd
  obtain ⟨P, l, hP⟩ := exists_conj_eq_HSL hx hx2
  refine ⟨P, l, hP, fun h => hx1 ?_⟩
  have h1 : P⁻¹ * x * P = 1 := by
    rw [hP, eq_one_of_val_eq_val_inv h]
    exact (hslHom k).map_one
  calc x = P * (P⁻¹ * x * P) * P⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem conj_mem_diagTorus_of_commute {x P B : SL2 k} {l : kˣ} (hP : P⁻¹ * x * P = HSL l)
    (hl : (l : k) ≠ ((l⁻¹ : kˣ) : k)) (hB : B * x = x * B) : P⁻¹ * B * P ∈ diagTorus k := by
  apply mem_diagTorus_of_commute hl
  rw [← hP]
  calc P⁻¹ * B * P * (P⁻¹ * x * P) = P⁻¹ * (B * x) * P := by group
    _ = P⁻¹ * (x * B) * P := by rw [hB]
    _ = P⁻¹ * x * P * (P⁻¹ * B * P) := by group

theorem trace_conj_SL2 (a b : SL2 k) :
    Matrix.trace ((a * b * a⁻¹ : SL2 k) : Matrix (Fin 2) (Fin 2) k) =
      Matrix.trace (b : Matrix (Fin 2) (Fin 2) k) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul a⁻¹ a, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    one_mul]

theorem trace_HSL (l : kˣ) :
    Matrix.trace ((HSL l : SL2 k) : Matrix (Fin 2) (Fin 2) k) = (l : k) + ((l⁻¹ : kˣ) : k) := by
  rw [Matrix.trace_fin_two, coe_HSL]
  simp

theorem eq_or_eq_inv_of_commute_of_trace {x P y : SL2 k} {l : kˣ} (hP : P⁻¹ * x * P = HSL l)
    (hl : (l : k) ≠ ((l⁻¹ : kˣ) : k)) (hy : y * x = x * y)
    (htr : Matrix.trace (y : Matrix (Fin 2) (Fin 2) k) =
      Matrix.trace (x : Matrix (Fin 2) (Fin 2) k)) : y = x ∨ y = x⁻¹ := by
  obtain ⟨m, hm⟩ := conj_mem_diagTorus_of_commute hP hl hy
  change HSL m = P⁻¹ * y * P at hm
  have htrP : ∀ z : SL2 k, Matrix.trace ((P⁻¹ * z * P : SL2 k) : Matrix (Fin 2) (Fin 2) k) =
      Matrix.trace (z : Matrix (Fin 2) (Fin 2) k) := fun z => by
    have h := trace_conj_SL2 P⁻¹ z
    rwa [inv_inv] at h
  have e : (m : k) + ((m⁻¹ : kˣ) : k) = (l : k) + ((l⁻¹ : kˣ) : k) := by
    rw [← trace_HSL, ← trace_HSL, hm, ← hP, htrP, htrP, htr]
  have hm1 : (m : k) * ((m⁻¹ : kˣ) : k) = 1 := Units.mul_inv m
  have hl1 : (l : k) * ((l⁻¹ : kˣ) : k) = 1 := Units.mul_inv l
  have hprod : ((m : k) - l) * ((m : k) - ((l⁻¹ : kˣ) : k)) = 0 := by
    linear_combination (m : k) * e - hm1 + hl1
  have hy' : y = P * HSL m * P⁻¹ := by rw [hm]; group
  have hx' : x = P * HSL l * P⁻¹ := by rw [← hP]; group
  rcases mul_eq_zero.1 hprod with h | h
  · left
    rw [hy', hx', Units.ext (sub_eq_zero.1 h)]
  · right
    have hml : m = l⁻¹ := Units.ext (sub_eq_zero.1 h)
    rw [hy', hx', hml, show (HSL l⁻¹ : SL2 k) = (HSL l)⁻¹ from (hslHom k).map_inv l]
    group

theorem isCyclic_of_forall_commute [Finite k] [CharP k 2] {x : SL2 k}
    (hx : x ^ (Nat.card k - 1) = 1) (hx1 : x ≠ 1) {S : Subgroup (SL2 k)}
    (hS : ∀ s ∈ S, s * x = x * s) : IsCyclic S := by
  obtain ⟨P, l, hP, hl⟩ := exists_conj_eq_HSL_of_ne_one hx hx1
  have hle : S ≤ (diagTorus k).map (MulAut.conj P).toMonoidHom := fun s hs =>
    ⟨P⁻¹ * s * P, conj_mem_diagTorus_of_commute hP hl (hS s hs), by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩
  have : IsCyclic ((diagTorus k).map (MulAut.conj P).toMonoidHom) := by
    rw [diagTorus, ← MonoidHom.range_comp]
    exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  exact Subgroup.isCyclic_of_le hle

theorem isCyclic_of_card_dvd_card_sub_one [Finite k] [CharP k 2] {H : Subgroup (SL2 k)}
    (hH : Nat.card H ∣ Nat.card k - 1) : IsCyclic H := by
  classical
  have := Fintype.ofFinite k
  have hpow : ∀ h ∈ H, h ^ (Nat.card k - 1) = 1 := fun h hh => by
    have h1 := orderOf_dvd_natCard (⟨h, hh⟩ : H)
    rw [Subgroup.orderOf_mk] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 (h1.trans hH)
  have hoddH : Odd (Nat.card H) := Odd.of_dvd_nat odd_card_sub_one_of_charP_two hH
  have key : ∀ x ∈ H, x ≠ 1 → (∀ h ∈ H, h * x = x * h) → IsCyclic H := fun x hxH hx1 hcomm =>
    isCyclic_of_forall_commute (hpow x hxH) hx1 hcomm
  by_cases hbot : H = ⊥
  · subst hbot
    infer_instance
  have hZ : IsZGroup H := by
    refine ⟨fun p hp S => ?_⟩
    have : Fact p.Prime := ⟨hp⟩
    by_cases hS : (S : Subgroup H) = ⊥
    · rw [hS]
      infer_instance
    have : Nontrivial (S : Subgroup H) := (Subgroup.nontrivial_iff_ne_bot _).2 hS
    have := IsPGroup.center_nontrivial S.2
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center (S : Subgroup H))
    set x : SL2 k := (((z : (S : Subgroup H)) : H) : SL2 k) with hxdef
    have hx1 : x ≠ 1 := fun h => hz (Subtype.ext (Subtype.ext (Subtype.ext h)))
    have hxH : x ∈ H := ((z : (S : Subgroup H)) : H).2
    set S' : Subgroup (SL2 k) := ((S : Subgroup H).map H.subtype) with hS'
    have hS'c : ∀ s ∈ S', s * x = x * s := by
      rintro _ ⟨s, hs, rfl⟩
      have h := Subgroup.mem_center_iff.1 z.2 ⟨s, hs⟩
      exact congrArg (fun w : (S : Subgroup H) => ((w : H) : SL2 k)) h
    have := isCyclic_of_forall_commute (hpow x hxH) hx1 hS'c
    exact isCyclic_of_surjective ((S : Subgroup H).equivMapOfInjective H.subtype
      H.subtype_injective).symm.toMonoidHom (MulEquiv.surjective _)
  obtain ⟨c, hc⟩ := (IsZGroup.isCyclic_commutator H).exists_generator
  by_cases hc1 : ((c : H) : SL2 k) = 1
  ·
    have hcomm : ∀ a b : H, a * b = b * a := by
      have hbot' : commutator H = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (hc ⟨y, hy⟩)
        have hc1' : c = 1 := Subtype.ext (Subtype.ext hc1)
        rw [hc1', one_zpow] at hn
        rw [mem_bot]
        exact (congrArg Subtype.val hn).symm
      rw [commutator_eq_bot_iff_center_eq_top] at hbot'
      intro a b
      exact (mem_center_iff.1 (hbot' ▸ mem_top b) a)
    obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1 hbot)
    refine key (y : SL2 k) y.2 (fun h => hy1 (Subtype.ext h)) fun h hh => ?_
    exact congrArg Subtype.val (hcomm ⟨h, hh⟩ y)
  ·
    set x : SL2 k := ((c : H) : SL2 k) with hxdef
    have hxH : x ∈ H := (c : H).2
    obtain ⟨P, l, hP, hl⟩ := exists_conj_eq_HSL_of_ne_one (hpow x hxH) hc1
    refine key x hxH hc1 fun h hh => ?_
    set h' : H := ⟨h, hh⟩
    have hmem : h' * (c : H) * h'⁻¹ ∈ commutator H :=
      (Subgroup.commutator_normal ⊤ ⊤).conj_mem _ c.2 h'
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (hc ⟨_, hmem⟩)
    have hconj : h * x * h⁻¹ = x ^ n := by
      have h1 := congrArg (fun w : commutator H => ((w : H) : SL2 k)) hn
      simp only [SubgroupClass.coe_zpow] at h1
      rw [h1]
      rfl
    have hcx : h * x * h⁻¹ * x = x * (h * x * h⁻¹) := by
      rw [hconj, ← zpow_add_one, ← zpow_one_add, add_comm]
    rcases eq_or_eq_inv_of_commute_of_trace hP hl hcx (trace_conj_SL2 h x) with h1 | h1
    · calc h * x = h * x * h⁻¹ * h := by group
        _ = x * h := by rw [h1]
    ·
      have h2 : h * h * x = x * (h * h) := by
        calc h * h * x = h * (h * x * h⁻¹) * h⁻¹ * (h * h) := by group
          _ = h * x⁻¹ * h⁻¹ * (h * h) := by rw [h1]
          _ = (h * x * h⁻¹)⁻¹ * (h * h) := by group
          _ = x * (h * h) := by rw [h1, inv_inv]
      have hodd : Odd (orderOf h) := by
        have h3 := orderOf_dvd_natCard h'
        rw [Subgroup.orderOf_mk] at h3
        exact Odd.of_dvd_nat hoddH h3
      obtain ⟨j, hj⟩ := hodd
      have hh' : h = (h * h) ^ (j + 1) := by
        rw [← sq, ← pow_mul, show 2 * (j + 1) = orderOf h + 1 by omega, pow_succ,
          pow_orderOf_eq_one, one_mul]
      rw [hh']
      exact ((Commute.pow_left h2 (j + 1)) : _)

end SL2

section Torus


variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem isCyclic_of_le_shortJ (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {X'' : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)} (hX : X'' ≤ shortJ k σ)
    (hcard : Nat.card X'' = Nat.card (w1C k σ)) : IsCyclic X'' := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP K 2 := charP_two_of_card hf hK
  have hk2 : (2 : k) = 0 := E6GraphHighestRoot.two_eq_zero_of_card hf hk
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hk2
  have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c =>
    (sigma_eq_self_iff hk hσ _).2 ⟨c, rfl⟩
  have hWC : shortRootTorus (algebraMap k K) ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    shortRootTorus_le_C0 hσι
  have hcardW : Nat.card (w1C k σ) = Nat.card k - 1 := by
    rw [w1C, Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv, card_shortRootTorus]
  set ι := algebraMap k K with hι
  set H : Subgroup (SL2 k) := (X''.map (graphFixedRootGroup TwistTag.E6 K σ).subtype).comap
    (jsMap ι) with hHdef
  have hXrange : X''.map (graphFixedRootGroup TwistTag.E6 K σ).subtype ≤ (jsMap ι).range := by
    rw [range_jsMap]
    rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.1 (hX hx)
  have hHmap : H.map (jsMap ι) = X''.map (graphFixedRootGroup TwistTag.E6 K σ).subtype :=
    map_comap_eq_self hXrange
  have hcardH : Nat.card H = Nat.card X'' := by
    rw [← card_map_of_injective (K := H) (jsMap_injective ι), hHmap,
      card_map_of_injective (graphFixedRootGroup TwistTag.E6 K σ).subtype_injective]
  have hcycH : IsCyclic H :=
    isCyclic_of_card_dvd_card_sub_one (by rw [hcardH, hcard, hcardW])
  exact isCyclic_of_surjective (((H.equivMapOfInjective (jsMap ι) (jsMap_injective ι)).trans
    (MulEquiv.subgroupCongr hHmap)).trans (X''.equivMapOfInjective _
      (graphFixedRootGroup TwistTag.E6 K σ).subtype_injective).symm).toMonoidHom
    (MulEquiv.surjective _)

theorem torusConjY_holds (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    TorusConjY k σ := by
  intro X'' hX hcard
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  ·
    have hf1' : f = 1 := by omega
    subst hf1'
    have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
    have : CharP K 2 := charP_two_of_card hf hK
    have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c =>
      (sigma_eq_self_iff hk hσ _).2 ⟨c, rfl⟩
    have hWC : shortRootTorus (algebraMap k K) ≤ graphFixedRootGroup TwistTag.E6 K σ :=
      shortRootTorus_le_C0 hσι
    have hcardW : Nat.card (w1C k σ) = 1 := by
      rw [w1C, Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv, card_shortRootTorus, hk]
      norm_num
    refine ⟨1, ?_⟩
    rw [eq_bot_of_card_eq X'' (hcard.trans hcardW), eq_bot_of_card_eq (w1C k σ) hcardW,
      Subgroup.map_bot]
  · obtain ⟨c, -, hc⟩ := exists_conj_eq_shortRootTorus_of_isCyclic hf2 hk hK hσ hX
      (isCyclic_of_le_shortJ hf hk hK hσ hX hcard) hcard
    exact ⟨c, hc⟩

end Torus

end CFSG.SeitzReduction.TwistedE6Pilot
