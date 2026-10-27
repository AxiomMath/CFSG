module

public import CFSG.SignalizerFunctorTheorem.Glauberman.External
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps345.SL23

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman

variable {G : Type*} [Group G] [Finite G]

section QuotientAux

variable {H : Type*} [Group H]

private theorem odd_card_primeSetCore_compl_two [Finite H] :
    Odd (Nat.card (primeSetCore (GroupType := H) ({2}ᶜ : Set ℕ))) := by
  by_contra hodd
  have hdvd : 2 ∣ Nat.card (primeSetCore (GroupType := H) ({2}ᶜ : Set ℕ)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  exact prime_set_core_supported (GroupType := H) ({2}ᶜ : Set ℕ) 2 Nat.prime_two hdvd
    (Set.mem_singleton 2)

private theorem eq_one_of_mem_inf_card_two_pow {A K : Subgroup H} {n : ℕ}
    (hA : Nat.card A = 2 ^ n) (hK : Odd (Nat.card K)) {z : H} (hzA : z ∈ A) (hzK : z ∈ K) :
    z = 1 := by
  have hcop : Nat.Coprime (Nat.card A) (Nat.card K) := by
    rw [hA]
    exact (Nat.coprime_two_left.mpr hK).pow_left n
  exact Subgroup.disjoint_def.mp (Subgroup.disjoint_of_coprime_natCard hcop) hzA hzK

private theorem mk'_eq_one_iff_mem (K : Subgroup H) [K.Normal] (x : H) :
    QuotientGroup.mk' K x = 1 ↔ x ∈ K := by
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']

private theorem eq_of_mk'_eq_card_two_pow (K : Subgroup H) [K.Normal] {A : Subgroup H} {n : ℕ}
    (hA : Nat.card A = 2 ^ n) (hK : Odd (Nat.card K)) {a b : H} (ha : a ∈ A) (hb : b ∈ A)
    (h : QuotientGroup.mk' K a = QuotientGroup.mk' K b) : a = b := by
  have h1 : a⁻¹ * b ∈ K :=
    (mk'_eq_one_iff_mem K _).mp (by rw [map_mul, map_inv, h, inv_mul_cancel])
  exact inv_mul_eq_one.mp (eq_one_of_mem_inf_card_two_pow hA hK (A.mul_mem (A.inv_mem ha) hb) h1)

private theorem elemAbelian_mul_comm_aux {q : ℕ} {E : Subgroup H} (hE : IsElemAbelian q E)
    {x y : H} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hE hx hy

private theorem isElemAbelian_of_forall_aux {q : ℕ} {E : Subgroup H}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ q = 1) :
    IsElemAbelian q E :=
  ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hcomm a a.2 b b.2), hexp⟩

private theorem isElemAbelian_map_aux {q : ℕ} {M N : Type*} [Group M] [Group N] {E : Subgroup M}
    (hE : IsElemAbelian q E) (f : M →* N) : IsElemAbelian q (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

private theorem isElemAbelian_comap_aux {q : ℕ} {M N : Type*} [Group M] [Group N]
    {E : Subgroup N} (hE : IsElemAbelian q E) (f : M →* N) (hf : Function.Injective f) :
    IsElemAbelian q (E.comap f) := by
  refine isElemAbelian_of_forall_aux ?_ ?_
  · intro x hx y hy
    apply hf
    rw [map_mul, map_mul]
    exact elemAbelian_mul_comm_aux hE hx hy
  · intro x hx
    apply hf
    rw [map_pow, map_one]
    exact hE.2 _ hx

private theorem exists_orderOf_eq_six_quotient [Finite H] (K : Subgroup H) [K.Normal]
    (hK : Odd (Nat.card K))
    (hD : ∃ D : Subgroup H, ∃ φ : D →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      Function.Surjective φ) :
    ∃ x : H ⧸ K, orderOf x = 6 := by
  obtain ⟨D, φ, hφ⟩ := hD
  obtain ⟨x, hx⟩ := exists_orderOf_eq_six_sl_two_three
  obtain ⟨y, rfl⟩ := hφ x
  have hNn : ((K.subgroupOf D).map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  have hodd : Odd (Nat.card ((K.subgroupOf D).map φ)) := by
    refine hK.of_dvd_nat ((Subgroup.card_map_dvd _ φ).trans ?_)
    have h1 : Nat.card ((K.subgroupOf D).map D.subtype) = Nat.card (K.subgroupOf D) :=
      Subgroup.card_map_of_injective D.subtype_injective
    rw [← h1]
    exact Subgroup.card_dvd_of_le (by rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left)
  have hbot : (K.subgroupOf D).map φ = ⊥ := eq_bot_of_normal_of_odd_card_sl_two_three _ hodd
  have hker : ∀ z : D, (z : H) ∈ K → φ z = 1 := fun z hz => by
    have hmem : φ z ∈ (K.subgroupOf D).map φ :=
      Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hz)
    rwa [hbot, Subgroup.mem_bot] at hmem
  obtain ⟨z, hz⟩ : ∃ z : H ⧸ K, QuotientGroup.mk' K (y : H) = z := ⟨_, rfl⟩
  have hyn : (y : H) ^ orderOf z ∈ K :=
    (mk'_eq_one_iff_mem K _).mp (by rw [map_pow, hz]; exact pow_orderOf_eq_one z)
  have h6 : orderOf (φ y) ∣ orderOf z := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    exact hker (y ^ orderOf z) hyn
  rw [hx] at h6
  exact ⟨z ^ (orderOf z / 6), orderOf_pow_orderOf_div (orderOf_pos z).ne' h6⟩

private theorem exists_quotient_fourGroup [Finite H] (K : Subgroup H) [K.Normal]
    (hK : Odd (Nat.card K))
    (hW : ∃ W : Subgroup H, IsElemAbelian 2 W ∧ Nat.card W = 4 ∧
      ∃ d : H, IsPGroup 3 (Subgroup.zpowers d) ∧ d ∈ Subgroup.normalizer (W : Set H) ∧
        ∀ w ∈ W, d * w * d⁻¹ = w → w = 1) :
    ∃ d : H ⧸ K, IsPGroup 3 (Subgroup.zpowers d) ∧ d ≠ 1 ∧
      ∃ W : Subgroup (H ⧸ K), W ≠ ⊥ ∧ IsElemAbelian 2 W ∧
        d ∈ Subgroup.normalizer (W : Set (H ⧸ K)) ∧
        ∀ w ∈ W, d * w * d⁻¹ = w → w = 1 := by
  obtain ⟨W, hWe, hW4, d, hd3, hdW, hfree⟩ := hW
  have hW4' : Nat.card W = 2 ^ 2 := by rw [hW4]; norm_num
  have hdW' : ∀ w ∈ W, d * w * d⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hdW w).mp hw
  have hWne : W ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hW4
    omega
  refine ⟨QuotientGroup.mk' K d, ?_, ?_, W.map (QuotientGroup.mk' K), ?_, ?_, ?_, ?_⟩
  · rw [← MonoidHom.map_zpowers]
    exact hd3.map _
  · intro h1
    have hW1 : ∀ w ∈ W, w = 1 := fun w hw =>
      hfree w hw (eq_of_mk'_eq_card_two_pow K hW4' hK (hdW' w hw) hw
        (by rw [map_mul, map_mul, h1, one_mul, map_inv, h1, inv_one, mul_one]))
    apply hWne
    rw [Subgroup.eq_bot_iff_forall]
    exact hW1
  · intro hbot
    obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
    have hmem : QuotientGroup.mk' K w ∈ W.map (QuotientGroup.mk' K) :=
      Subgroup.mem_map_of_mem _ hw
    rw [hbot, Subgroup.mem_bot, mk'_eq_one_iff_mem] at hmem
    exact hw1 (Subtype.ext (eq_one_of_mem_inf_card_two_pow hW4' hK hw hmem))
  · exact isElemAbelian_map_aux hWe _
  · exact Subgroup.le_normalizer_map (QuotientGroup.mk' K) (Subgroup.mem_map_of_mem _ hdW)
  · rintro _ ⟨x, hxW, rfl⟩ hfix
    have hx1 : x = 1 := hfree x hxW (eq_of_mk'_eq_card_two_pow K hW4' hK (hdW' x hxW) hxW
      (by simpa only [map_mul, map_inv] using hfix))
    rw [hx1, map_one]

private theorem exists_elemAbelian_eight_of_quotient [Finite H] (K : Subgroup H) [K.Normal]
    (hK : Odd (Nat.card K)) {E : Subgroup (H ⧸ K)} (hE : IsElemAbelian 2 E)
    (hE8 : Nat.card E = 8) :
    ∃ E' : Subgroup H, IsElemAbelian 2 E' ∧ Nat.card E' = 8 := by
  have hdvd : 2 ^ 3 ∣ Nat.card (E.comap (QuotientGroup.mk' K)) := by
    have h := Subgroup.card_dvd_of_surjective
      (MonoidHom.subgroupComap_surjective (QuotientGroup.mk' K) E (QuotientGroup.mk'_surjective K))
    rw [hE8] at h
    simpa using h
  obtain ⟨P, hP, -, hPle⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := (⊥ : Subgroup H)) (by rw [Subgroup.card_bot]; exact one_dvd _) hdvd bot_le
  have hPE : ∀ x ∈ P, QuotientGroup.mk' K x ∈ E := fun x hx => hPle hx
  refine ⟨P, isElemAbelian_of_forall_aux ?_ ?_, by rw [hP]; norm_num⟩
  · intro x hx y hy
    refine eq_of_mk'_eq_card_two_pow K hP hK (P.mul_mem hx hy) (P.mul_mem hy hx) ?_
    rw [map_mul, map_mul]
    exact elemAbelian_mul_comm_aux hE (hPE x hx) (hPE y hy)
  · intro x hx
    refine eq_of_mk'_eq_card_two_pow K hP hK (P.pow_mem hx 2) P.one_mem ?_
    rw [map_pow, map_one]
    exact hE.2 _ (hPE x hx)

private theorem exists_elemAbelian_eight_of_core [Finite H] [Group.IsSolvable H]
    (K : Subgroup H) [K.Normal] (hK : Odd (Nat.card K))
    (hcore : primeSetCore (GroupType := H ⧸ K) ({2}ᶜ : Set ℕ) = ⊥)
    (hD : ∃ D : Subgroup H, ∃ φ : D →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      Function.Surjective φ)
    (hW : ∃ W : Subgroup H, IsElemAbelian 2 W ∧ Nat.card W = 4 ∧
      ∃ d : H, IsPGroup 3 (Subgroup.zpowers d) ∧ d ∈ Subgroup.normalizer (W : Set H) ∧
        ∀ w ∈ W, d * w * d⁻¹ = w → w = 1) :
    ∃ E : Subgroup H, IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  obtain ⟨d, hd3, hd1, W, hW0, hWe, hdW, hfree⟩ := exists_quotient_fourGroup K hK hW
  obtain ⟨E, hE, hE8⟩ := exists_elemAbelian_eight hcore
    (exists_orderOf_eq_six_quotient K hK hD) hd3 hd1 hW0 hWe hdW hfree
  exact exists_elemAbelian_eight_of_quotient K hK hE hE8

end QuotientAux

theorem exists_elemAbelian_eight_of_sections (C : Subgroup G) [Group.IsSolvable C]
    (hD : ∃ D : Subgroup G, D ≤ C ∧
      ∃ φ : D →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), Function.Surjective φ)
    (hW : ∃ W : Subgroup G, W ≤ C ∧ IsElemAbelian 2 W ∧ Nat.card W = 4 ∧
      ∃ d ∈ C, IsPGroup 3 (Subgroup.zpowers d) ∧ d ∈ Subgroup.normalizer (W : Set G) ∧
        ∀ w ∈ W, d * w * d⁻¹ = w → w = 1) :
    ∃ E : Subgroup G, E ≤ C ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  obtain ⟨D, hDC, φ, hφ⟩ := hD
  obtain ⟨W, hWC, hWe, hW4, d, hdC, hd3, hdW, hfree⟩ := hW
  have hKn : (primeSetCore (GroupType := C) ({2}ᶜ : Set ℕ)).Normal := prime_set_core_normal _
  have hD' : ∃ D' : Subgroup C, ∃ φ' : D' →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      Function.Surjective φ' :=
    ⟨D.subgroupOf C, φ.comp (Subgroup.subgroupOfEquivOfLe hDC).toMonoidHom,
      hφ.comp (Subgroup.subgroupOfEquivOfLe hDC).surjective⟩
  have hd3' : IsPGroup 3 (Subgroup.zpowers (⟨d, hdC⟩ : C)) :=
    (hd3.comap_of_injective C.subtype C.subtype_injective).to_le
      (Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers d))
  have hdW' : (⟨d, hdC⟩ : C) ∈ Subgroup.normalizer ((W.subgroupOf C : Subgroup C) : Set C) :=
    Subgroup.le_normalizer_comap C.subtype (Subgroup.mem_comap.mpr hdW)
  have hW' : ∃ W' : Subgroup C, IsElemAbelian 2 W' ∧ Nat.card W' = 4 ∧
      ∃ d' : C, IsPGroup 3 (Subgroup.zpowers d') ∧ d' ∈ Subgroup.normalizer (W' : Set C) ∧
        ∀ w ∈ W', d' * w * d'⁻¹ = w → w = 1 :=
    ⟨W.subgroupOf C, isElemAbelian_comap_aux hWe C.subtype C.subtype_injective,
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv).trans hW4, ⟨d, hdC⟩, hd3', hdW',
      fun w hw hfix => Subtype.ext (hfree (w : G) hw (congrArg Subtype.val hfix))⟩
  obtain ⟨E, hE, hE8⟩ := exists_elemAbelian_eight_of_core
    (primeSetCore (GroupType := C) ({2}ᶜ : Set ℕ)) odd_card_primeSetCore_compl_two
    (prime_set_core_quotient_trivial (GroupType := C) ({2}ᶜ : Set ℕ)) hD' hW'
  exact ⟨E.map C.subtype, Subgroup.map_subtype_le E, isElemAbelian_map_aux hE _,
    by rw [Subgroup.card_map_of_injective C.subtype_injective]; exact hE8⟩

end CFSG.SignalizerFunctorTheorem.Glauberman
