module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin.SteinbergCG

open Equiv Module

theorem perm_three_centralizer_involution : ∀ t : Perm (Fin 3), t ≠ 1 → t * t = 1 →
    ∀ g : Perm (Fin 3), g * t = t * g → g = 1 ∨ g = t := by
  decide

theorem eq_one_or_eq_of_card_two {G : Type*} [Group G] {T : Subgroup G} (hT : Nat.card T = 2)
    {t : G} (htT : t ∈ T) (ht1 : t ≠ 1) {x : G} (hxT : x ∈ T) : x = 1 ∨ x = t := by
  classical
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  have : Fintype T := Fintype.ofFinite T
  by_contra h
  push Not at h
  have hcard : ({⟨1, T.one_mem⟩, ⟨t, htT⟩, ⟨x, hxT⟩} : Finset T).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h' => h.2 (congrArg Subtype.val h').symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h' => ht1 (congrArg Subtype.val h').symm,
        fun h' => h.1 (congrArg Subtype.val h').symm⟩
  have h2 := Finset.card_le_univ ({⟨1, T.one_mem⟩, ⟨t, htT⟩, ⟨x, hxT⟩} : Finset T)
  rw [hcard, ← Nat.card_eq_fintype_card, hT] at h2
  omega

theorem normalizer_eq_of_card_two_perm_three {T : Subgroup (Perm (Fin 3))} (hT : Nat.card T = 2) :
    Subgroup.normalizer (T : Set (Perm (Fin 3))) = T := by
  classical
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by rw [hT]; norm_num)
  obtain ⟨⟨t, htT⟩, ht⟩ := exists_ne (1 : T)
  have ht1 : t ≠ 1 := fun h => ht (Subtype.ext h)
  have htt : t * t = 1 := by
    have h1 : (⟨t, htT⟩ : T) ^ Nat.card T = 1 := pow_card_eq_one'
    rw [hT, pow_two] at h1
    exact congrArg Subtype.val h1
  apply le_antisymm _ Subgroup.le_normalizer
  intro g hg
  have h1 : g * t * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hg t).mp htT
  have h2 : g * t * g⁻¹ ≠ 1 := fun h => ht1 (by
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [mul_assoc] using this)
  have h3 : g * t * g⁻¹ = t := (eq_one_or_eq_of_card_two hT htT ht1 h1).resolve_left h2
  have h4 : g * t = t * g := by
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h3]
  rcases perm_three_centralizer_involution t ht1 htt g h4 with rfl | rfl
  · exact T.one_mem
  · exact htT

@[expose] def s7u₁ : Perm (Fin 7) := swap 0 2 * swap 1 3

@[expose] def s7u₂ : Perm (Fin 7) := swap 4 5

@[expose] def s7a : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3

@[expose] def s7b : Perm (Fin 7) := swap 1 3

@[expose] def s7R : Subgroup (Perm (Fin 7)) :=
  Subgroup.centralizer {s7u₁} ⊓ Subgroup.centralizer {s7u₂}

theorem mem_s7R {g : Perm (Fin 7)} : g ∈ s7R ↔ g * s7u₁ = s7u₁ * g ∧ g * s7u₂ = s7u₂ * g := by
  rw [s7R, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]

set_option maxRecDepth 100000 in
theorem s7_normalizer_check : ∀ g : Perm (Fin 7),
    ((g * s7a * g⁻¹) * s7u₁ = s7u₁ * (g * s7a * g⁻¹) ∧
      (g * s7a * g⁻¹) * s7u₂ = s7u₂ * (g * s7a * g⁻¹)) →
    ((g * s7b * g⁻¹) * s7u₁ = s7u₁ * (g * s7b * g⁻¹) ∧
      (g * s7b * g⁻¹) * s7u₂ = s7u₂ * (g * s7b * g⁻¹)) →
    ((g * s7u₂ * g⁻¹) * s7u₁ = s7u₁ * (g * s7u₂ * g⁻¹) ∧
      (g * s7u₂ * g⁻¹) * s7u₂ = s7u₂ * (g * s7u₂ * g⁻¹)) →
    g * s7u₁ = s7u₁ * g ∧ g * s7u₂ = s7u₂ * g := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem card_s7R_filter : (Finset.univ.filter fun g : Perm (Fin 7) =>
    g * s7u₁ = s7u₁ * g ∧ g * s7u₂ = s7u₂ * g).card = 16 := by
  decide +kernel

theorem card_s7R : Nat.card s7R = 16 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_s7R), Nat.card_eq_fintype_card,
    Fintype.card_subtype, card_s7R_filter]

theorem s7R_normalizer : Subgroup.normalizer (s7R : Set (Perm (Fin 7))) = s7R := by
  apply le_antisymm _ Subgroup.le_normalizer
  intro g hg
  have ha : g * s7a * g⁻¹ ∈ s7R :=
    (Subgroup.mem_normalizer_iff.mp hg _).mp (mem_s7R.mpr (by decide))
  have hb : g * s7b * g⁻¹ ∈ s7R :=
    (Subgroup.mem_normalizer_iff.mp hg _).mp (mem_s7R.mpr (by decide))
  have hu : g * s7u₂ * g⁻¹ ∈ s7R :=
    (Subgroup.mem_normalizer_iff.mp hg _).mp (mem_s7R.mpr (by decide))
  exact mem_s7R.mpr (s7_normalizer_check g (mem_s7R.mp ha) (mem_s7R.mp hb) (mem_s7R.mp hu))

theorem factorization_card_perm_seven : (Nat.card (Perm (Fin 7))).factorization 2 = 4 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h : (Nat.factorial 7) = 2 ^ 4 * 315 := by decide
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp only [Finsupp.single_eq_same]
  have h315 : (Nat.factorization 315) 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  omega

theorem factorization_card_perm_three : (Nat.card (Perm (Fin 3))).factorization 2 = 1 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h : Nat.factorial 3 = 2 ^ 1 * 3 := by decide
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp only [Finsupp.single_eq_same]
  have h3 : (Nat.factorization 3) 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  omega

theorem normalizer_eq_of_card_sixteen_perm_seven {T : Subgroup (Perm (Fin 7))}
    (hT : Nat.card T = 16) : Subgroup.normalizer (T : Set (Perm (Fin 7))) = T := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h16 : ∀ {P : Subgroup (Perm (Fin 7))}, Nat.card P = 16 →
      Nat.card P = 2 ^ (Nat.card (Perm (Fin 7))).factorization 2 := fun h => by
    rw [h, factorization_card_perm_seven]
    rfl
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (Perm (Fin 7)) (Sylow.ofCard s7R (h16 card_s7R))
    (Sylow.ofCard T (h16 hT))
  have hTeq : T = s7R.map (MulAut.conj h).toMonoidHom := by
    have h1 := congrArg (fun P : Sylow 2 (Perm (Fin 7)) => (P : Subgroup (Perm (Fin 7)))) hh
    simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at h1
    rw [← h1]
    rfl
  rw [hTeq, ← Subgroup.map_equiv_normalizer_eq, s7R_normalizer]

theorem normalizer_inf_eq_of_mulEquiv {G Q : Type*} [Group G] [Group Q] {H T : Subgroup G}
    (hTH : T ≤ H) (e : H ≃* Q)
    (hQ : Subgroup.normalizer (((T.subgroupOf H).map e.toMonoidHom : Subgroup Q) : Set Q) =
      (T.subgroupOf H).map e.toMonoidHom) :
    Subgroup.normalizer (T : Set G) ⊓ H = T := by
  apply le_antisymm
  · rintro x ⟨hxN, hxH⟩
    have h1 : (⟨x, hxH⟩ : H) ∈ Subgroup.normalizer ((T.subgroupOf H : Subgroup H) : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp hxN) h
    have h2 : e ⟨x, hxH⟩ ∈ Subgroup.normalizer
        (((T.subgroupOf H).map e.toMonoidHom : Subgroup Q) : Set Q) := by
      rw [← Subgroup.map_equiv_normalizer_eq]
      exact ⟨_, h1, rfl⟩
    rw [hQ] at h2
    obtain ⟨y, hy, hye⟩ := h2
    have hyx : y = ⟨x, hxH⟩ := e.injective hye
    rw [hyx, SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
    exact hy
  · exact le_inf Subgroup.le_normalizer hTH

theorem card_map_subgroupOf {G Q : Type*} [Group G] [Group Q] {H T : Subgroup G}
    (hTH : T ≤ H) (e : H ≃* Q) :
    Nat.card ((T.subgroupOf H).map e.toMonoidHom) = Nat.card T := by
  rw [Subgroup.card_map_of_injective e.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv

section GLTwo

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def nonzeroPerm : (V ≃ₗ[ZMod 2] V) →* Perm {v : V // v ≠ 0} where
  toFun g := g.toEquiv.subtypeEquiv fun v => by simp
  map_one' := by ext; rfl
  map_mul' g h := by ext; rfl

theorem nonzeroPerm_injective : Function.Injective (nonzeroPerm (V := V)) := by
  intro g h hgh
  ext v
  by_cases hv : v = 0
  · rw [hv, map_zero, map_zero]
  · have := congrArg (fun σ : Perm {v : V // v ≠ 0} => ((σ ⟨v, hv⟩ : {v : V // v ≠ 0}) : V)) hgh
    exact this

theorem nonempty_mulEquiv_perm_three [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 2) : Nonempty ((V ≃ₗ[ZMod 2] V) ≃* Perm (Fin 3)) := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Fintype V := Fintype.ofFinite V
  have hV4 : Nat.card V = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hV, Nat.card_zmod]
    norm_num
  have h3 : Nat.card {v : V // v ≠ 0} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hV4]
  have h6 : Nat.card (V ≃ₗ[ZMod 2] V) = 6 := by
    let bV := Module.finBasisOfFinrankEq (ZMod 2) V hV
    have h1 : Nat.card (V ≃ₗ[ZMod 2] V) =
        Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) :=
      (Nat.card_congr ((Matrix.GeneralLinearGroup.toLin' bV).toEquiv.trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toEquiv)).symm
    rw [h1, Matrix.card_GL_field, ZMod.card]
    decide
  have hfin : Finite (V ≃ₗ[ZMod 2] V) := Nat.finite_of_card_ne_zero (by rw [h6]; norm_num)
  have hbij : Function.Bijective (nonzeroPerm (V := V)) := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨nonzeroPerm_injective, ?_⟩
    rw [h6, Nat.card_perm, h3]
    rfl
  let e3 : {v : V // v ≠ 0} ≃ Fin 3 := Finite.equivFinOfCardEq h3
  exact ⟨(MulEquiv.ofBijective _ hbij).trans (Equiv.permCongrHom e3)⟩

end GLTwo

theorem exists_injective_pi_perm_three {m : ℕ} (hm : 9 ≤ m) :
    ∃ ι : (Fin 3 → Perm (Fin 3)) →* Perm (Fin m), Function.Injective ι := by
  classical
  have hcard : Fintype.card (Σ _ : Fin 3, Fin 3) ≤ Fintype.card (Fin m) := by
    simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let f : (Σ _ : Fin 3, Fin 3) ≃ {x : Fin m // x ∈ Set.range e} := Equiv.ofInjective e e.injective
  exact ⟨(Perm.extendDomainHom f).comp (Perm.sigmaCongrRightHom fun _ => Fin 3),
    (Perm.extendDomainHom_injective f).comp (Perm.sigmaCongrRightHom_injective)⟩

theorem exists_isElementaryAbelian_card_pRank {p : ℕ} (hp : p.Prime) (K : Type*) [Group K]
    [Finite K] :
    ∃ A : Subgroup K, CFSG.IsElementaryAbelian p A ∧ Nat.card A = p ^ CFSG.pRank p K := by
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (G := K) hp.one_lt ⊤
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact ⟨E, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).mpr hE, hcard⟩

end CFSG.Quasithin.SteinbergCG
