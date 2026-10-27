module

public import CFSG.Quasithin.SteinbergCDUnitaryThreeSylowSixteen

public section

namespace CFSG.LocalAnalysis.SteinbergCD

open Module Matrix CFSG.Quasithin.SteinbergCD

section Involution

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] (h2 : (2 : F) ≠ 0)

@[expose] def fixSp (f : V →ₗ[F] V) : Submodule F V := LinearMap.ker (f - LinearMap.id)

@[expose] def negSp (f : V →ₗ[F] V) : Submodule F V := LinearMap.ker (f + LinearMap.id)

theorem mem_fixSp {f : V →ₗ[F] V} {v : V} : v ∈ fixSp f ↔ f v = v := by
  rw [fixSp, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_negSp {f : V →ₗ[F] V} {v : V} : v ∈ negSp f ↔ f v = -v := by
  rw [negSp, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]

include h2 in
theorem isCompl_fixSp_negSp {f : V →ₗ[F] V} (hf : ∀ v, f (f v) = v) :
    IsCompl (fixSp f) (negSp f) := by
  refine ⟨Submodule.disjoint_def.2 fun v hv hv' => ?_, codisjoint_iff.2 (eq_top_iff.2
    fun v _ => Submodule.mem_sup.2 ⟨(2 : F)⁻¹ • (v + f v), ?_, (2 : F)⁻¹ • (v - f v), ?_, ?_⟩)⟩
  · rw [mem_fixSp] at hv
    rw [mem_negSp, hv] at hv'
    have h : (2 : F) • v = 0 := by rw [two_smul]; nth_rewrite 2 [hv']; exact add_neg_cancel v
    exact (smul_eq_zero.1 h).resolve_left h2
  · rw [mem_fixSp, map_smul, map_add, hf, add_comm]
  · rw [mem_negSp, map_smul, map_sub, hf, ← smul_neg, neg_sub]
  · rw [← smul_add, show v + f v + (v - f v) = (2 : F) • v by rw [two_smul]; abel, smul_smul,
      inv_mul_cancel₀ h2, one_smul]

include h2 in
theorem det_eq_neg_one_pow [FiniteDimensional F V] {f : V →ₗ[F] V} (hf : ∀ v, f (f v) = v) :
    LinearMap.det f = (-1) ^ finrank F (negSp f) := by
  have hc := isCompl_fixSp_negSp h2 hf
  set e := Submodule.prodEquivOfIsCompl _ _ hc
  have hfe : f = (e : (fixSp f × negSp f) →ₗ[F] V) ∘ₗ
      (LinearMap.prodMap LinearMap.id (-LinearMap.id)) ∘ₗ (e.symm : V →ₗ[F] _) := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨⟨x, y⟩, rfl⟩ := e.surjective v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
      LinearMap.neg_apply, LinearMap.id_apply, Submodule.coe_prodEquivOfIsCompl',
      Submodule.coe_prodEquivOfIsCompl', map_add, mem_fixSp.1 x.2, mem_negSp.1 y.2,
      Submodule.coe_neg]
  nth_rewrite 1 [hfe]
  rw [LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, one_mul,
    show (-LinearMap.id : negSp f →ₗ[F] negSp f) = (-1 : F) • LinearMap.id by
      ext; simp, LinearMap.det_smul, LinearMap.det_id, mul_one]

theorem map_mem_fixSp_of_comm {f g : V →ₗ[F] V} (hfg : f ∘ₗ g = g ∘ₗ f) {v : V}
    (hv : v ∈ fixSp f) : g v ∈ fixSp f := by
  rw [mem_fixSp] at hv ⊢
  rw [← LinearMap.comp_apply, hfg, LinearMap.comp_apply, hv]

end Involution

section Bound

variable {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)

include h2 in
theorem finrank_fixSp_eq_one {f : (Fin 3 → F) →ₗ[F] (Fin 3 → F)} (hf : ∀ v, f (f v) = v)
    (hdet : LinearMap.det f = 1) (hf1 : f ≠ LinearMap.id) :
    finrank F (fixSp f) = 1 ∧ finrank F (negSp f) = 2 := by
  have hc := isCompl_fixSp_negSp h2 hf
  have hsum : finrank F (fixSp f) + finrank F (negSp f) = 3 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (fixSp f) (negSp f)
    rw [hc.sup_eq_top, hc.inf_eq_bot, finrank_top, finrank_bot, add_zero, finrank_fin_fun] at this
    exact this.symm
  have hpow := det_eq_neg_one_pow h2 hf
  rw [hdet] at hpow
  have heven : Even (finrank F (negSp f)) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at hpow
    apply h2
    linear_combination hpow
  have hne : finrank F (negSp f) ≠ 0 := by
    intro h0
    apply hf1
    have htop : fixSp f = ⊤ := by
      rw [← hc.sup_eq_top, Submodule.finrank_eq_zero.1 h0, sup_bot_eq]
    exact LinearMap.ext fun v => mem_fixSp.1 (htop ▸ Submodule.mem_top)
  obtain ⟨k, hk⟩ := heven
  omega

include h2 in
theorem card_le_four_of_det_one {G : Type*} [Group G] [Finite G] (ρ : G →* GL (Fin 3) F)
    (hρ : Function.Injective ρ) (hdet : ∀ g, (ρ g).det = 1) (hcomm : ∀ x y : G, x * y = y * x)
    (hsq : ∀ x : G, x ^ 2 = 1) : Nat.card G ≤ 4 := by
  classical
  set φ : G → ((Fin 3 → F) →ₗ[F] (Fin 3 → F)) := fun g => toLin' ((ρ g : Matrix _ _ F))
  have hφmul : ∀ g h, φ (g * h) = φ g ∘ₗ φ h := fun g h => by
    simp only [φ, map_mul, Units.val_mul, toLin'_mul]
  have hφone : φ 1 = LinearMap.id := by simp [φ]
  have hφinj : Function.Injective φ := fun g h hgh => hρ (Units.ext
    (toLin'.injective hgh))
  have hinv : ∀ g v, φ g (φ g v) = v := fun g v => by
    rw [← LinearMap.comp_apply, ← hφmul, ← sq, hsq, hφone, LinearMap.id_apply]
  have hdet' : ∀ g, LinearMap.det (φ g) = 1 := fun g => by
    simp only [φ]
    rw [LinearMap.det_toLin', ← GeneralLinearGroup.val_det_apply, hdet g, Units.val_one]
  have hcommφ : ∀ g h, φ g ∘ₗ φ h = φ h ∘ₗ φ g := fun g h => by
    rw [← hφmul, ← hφmul, hcomm]
  have hdim : ∀ g, g ≠ 1 → finrank F (fixSp (φ g)) = 1 ∧ finrank F (negSp (φ g)) = 2 :=
    fun g hg => finrank_fixSp_eq_one h2 (hinv g) (hdet' g)
      (fun h => hg (hφinj (h.trans hφone.symm)))
  have hline : ∀ g h, g ≠ 1 → h ≠ 1 → fixSp (φ g) = fixSp (φ h) → g = h := by
    intro g h hg hh hgh
    by_contra hne
    have hgh1 : g * h ≠ 1 := fun e => hne (by
      have := eq_inv_of_mul_eq_one_left e
      rwa [show h⁻¹ = h from inv_eq_of_mul_eq_one_left (by rw [← sq, hsq])] at this)
    obtain ⟨hg1, hg2⟩ := hdim g hg
    obtain ⟨-, hh2⟩ := hdim h hh
    obtain ⟨hgh1', -⟩ := hdim (g * h) hgh1
    have hle : fixSp (φ g) ⊔ (negSp (φ g) ⊓ negSp (φ h)) ≤ fixSp (φ (g * h)) := by
      refine sup_le (fun v hv => ?_) (fun v hv => ?_)
      · have hv' : v ∈ fixSp (φ h) := hgh ▸ hv
        rw [mem_fixSp, hφmul, LinearMap.comp_apply, mem_fixSp.1 hv', mem_fixSp.1 hv]
      · rw [mem_fixSp, hφmul, LinearMap.comp_apply, mem_negSp.1 hv.2, map_neg,
          mem_negSp.1 hv.1, neg_neg]
    have hint : 1 ≤ finrank F (negSp (φ g) ⊓ negSp (φ h) : Submodule F (Fin 3 → F)) := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq (negSp (φ g)) (negSp (φ h))
      have h3 := Submodule.finrank_le (negSp (φ g) ⊔ negSp (φ h))
      rw [finrank_fin_fun] at h3
      omega
    have hdisj : fixSp (φ g) ⊓ (negSp (φ g) ⊓ negSp (φ h)) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [← (isCompl_fixSp_negSp h2 (hinv g)).inf_eq_bot]
      exact ⟨hv.1, hv.2.1⟩
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq (fixSp (φ g))
      (negSp (φ g) ⊓ negSp (φ h))
    rw [hdisj, finrank_bot, add_zero] at h4
    have h5 := Submodule.finrank_mono hle
    omega
  have hneg : ∀ g h, g ≠ 1 → h ≠ 1 → g ≠ h → fixSp (φ g) ≤ negSp (φ h) := by
    intro g h hg hh hgh
    have hc := isCompl_fixSp_negSp h2 (hinv h)
    obtain ⟨hg1, -⟩ := hdim g hg
    obtain ⟨hh1, -⟩ := hdim h hh
    have hsplit : fixSp (φ g) = (fixSp (φ g) ⊓ fixSp (φ h)) ⊔ (fixSp (φ g) ⊓ negSp (φ h)) := by
      refine le_antisymm (fun v hv => ?_) (sup_le inf_le_left inf_le_left)
      have hv1 : (2 : F)⁻¹ • (v + φ h v) ∈ fixSp (φ g) ⊓ fixSp (φ h) := ⟨Submodule.smul_mem _ _
        (Submodule.add_mem _ hv (map_mem_fixSp_of_comm (hcommφ g h) hv)),
          mem_fixSp.2 (by rw [map_smul, map_add, hinv, add_comm])⟩
      have hv2 : (2 : F)⁻¹ • (v - φ h v) ∈ fixSp (φ g) ⊓ negSp (φ h) := ⟨Submodule.smul_mem _ _
        (Submodule.sub_mem _ hv (map_mem_fixSp_of_comm (hcommφ g h) hv)),
          mem_negSp.2 (by rw [map_smul, map_sub, hinv, ← smul_neg, neg_sub])⟩
      have e : v = (2 : F)⁻¹ • (v + φ h v) + (2 : F)⁻¹ • (v - φ h v) := by
        rw [← smul_add, show v + φ h v + (v - φ h v) = (2 : F) • v by rw [two_smul]; abel,
          smul_smul, inv_mul_cancel₀ h2, one_smul]
      rw [e]
      exact Submodule.add_mem_sup hv1 hv2
    have hdisj : (fixSp (φ g) ⊓ fixSp (φ h)) ⊓ (fixSp (φ g) ⊓ negSp (φ h)) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [← hc.inf_eq_bot]
      exact ⟨hv.1.2, hv.2.2⟩
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (fixSp (φ g) ⊓ fixSp (φ h))
      (fixSp (φ g) ⊓ negSp (φ h))
    rw [← hsplit, hdisj, finrank_bot, add_zero, hg1] at hsum
    have hfix0 : finrank F (fixSp (φ g) ⊓ fixSp (φ h) : Submodule F (Fin 3 → F)) = 0 := by
      by_contra hne
      have h1 : finrank F (fixSp (φ g) ⊓ fixSp (φ h) : Submodule F (Fin 3 → F)) = 1 := by omega
      have he1 : fixSp (φ g) ⊓ fixSp (φ h) = fixSp (φ g) :=
        Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, hg1])
      have he2 : fixSp (φ g) ⊓ fixSp (φ h) = fixSp (φ h) :=
        Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h1, hh1])
      exact hgh (hline g h hg hh (he1.symm.trans he2))
    have hn1 : finrank F (fixSp (φ g) ⊓ negSp (φ h) : Submodule F (Fin 3 → F)) =
        finrank F (fixSp (φ g)) := by omega
    have := Submodule.eq_of_le_of_finrank_eq inf_le_left hn1
    rw [← this]
    exact inf_le_right
  by_contra hcard
  push Not at hcard
  have := Fintype.ofFinite G
  have hc5 : 5 ≤ (Finset.univ : Finset G).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1} : Finset G)) (t := (Finset.univ : Finset G))
    (by rw [Finset.card_singleton]; omega)
  obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, x} : Finset G)) (t := (Finset.univ : Finset G))
    ((Finset.card_le_two).trans_lt (by omega))
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, x, y, x * y} : Finset G)) (t := (Finset.univ : Finset G))
    (Finset.card_le_four.trans_lt (by omega))
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hx hy hz
  obtain ⟨hy1, hyx⟩ := hy
  obtain ⟨hz1, hzx, hzy, hzxy⟩ := hz
  have hxy1 : x * y ≠ 1 := fun e => hyx (by
    have := eq_inv_of_mul_eq_one_right e
    rwa [show x⁻¹ = x from inv_eq_of_mul_eq_one_left (by rw [← sq, hsq])] at this)
  have hzx' := hneg z x hz1 hx hzx
  have hzy' := hneg z y hz1 hy1 hzy
  have hle : fixSp (φ z) ≤ fixSp (φ (x * y)) := fun v hv => by
    rw [mem_fixSp, hφmul, LinearMap.comp_apply, mem_negSp.1 (hzy' hv), map_neg,
      mem_negSp.1 (hzx' hv), neg_neg]
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [(hdim z hz1).1, (hdim _ hxy1).1])
  exact hzxy (hline z (x * y) hz1 hxy1 heq)

include h2 in
theorem card_le_four_of_quotient {S : Type*} [Group S] [Finite S] (ρ : S →* GL (Fin 3) F)
    (hρ : Function.Injective ρ) (hdet : ∀ g, (ρ g).det = 1) {Z : Subgroup S} [Z.Normal]
    (hZ : ∀ z ∈ Z, z ^ 3 = 1) (A : Subgroup (S ⧸ Z)) [hA : IsElementaryAbelian 2 A] :
    Nat.card A ≤ 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' Z
  set At := A.comap π
  let g : At →* A := (π.comp At.subtype).codRestrict A fun x => x.2
  have hg : Function.Surjective g := fun a => by
    obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective Z (a : S ⧸ Z)
    exact ⟨⟨s, by simp [At, π, hs]⟩, Subtype.ext hs⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 At) := inferInstance
  have hinj : Function.Injective (g.comp (P : Subgroup At).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : (((x : At) : S)) ∈ Z := by
      have : π ((x : At) : S) = 1 := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff _).1 this
    have h3 := hZ _ hxZ
    obtain ⟨k, hk⟩ := P.isPGroup' x
    have hk' : (((x : At) : S)) ^ 2 ^ k = 1 := by
      have := congrArg (fun y : (P : Subgroup At) => ((y : At) : S)) hk
      simpa using this
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have h1 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
      (orderOf_dvd_of_pow_eq_one h3)
    exact Subtype.ext (Subtype.ext (orderOf_eq_one_iff.1 h1))
  have hA2 : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  have hsurj : Function.Surjective (g.comp (P : Subgroup At).subtype) := by
    have hQ := (P.mapSurjective hg).card_eq_multiplicity
    rw [Sylow.coe_mapSurjective] at hQ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hA2
    have htop : (P : Subgroup At).map g = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      rw [hQ, hn, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        Nat.Prime.factorization_self Nat.prime_two, mul_one]
    intro a
    have ha : a ∈ (P : Subgroup At).map g := htop ▸ Subgroup.mem_top a
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨⟨x, hx⟩, rfl⟩
  have e : (P : Subgroup At) ≃* A := MulEquiv.ofBijective _ ⟨hinj, hsurj⟩
  rw [← Nat.card_congr e.toEquiv]
  refine card_le_four_of_det_one h2 (ρ.comp (At.subtype.comp (P : Subgroup At).subtype))
    (hρ.comp (At.subtype_injective.comp (P : Subgroup At).subtype_injective)) (fun x => hdet _)
    (fun x y => e.injective ?_) (fun x => e.injective ?_)
  · rw [map_mul, map_mul]
    exact (hA.is_comm.comm _ _)
  · rw [map_pow, map_one]
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) _ (e x).2)

end Bound

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank

theorem card_le_ordProj_of_isPGroup {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsPGroup 2 P) : Nat.card P ≤ ordProj[2] (Nat.card G) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  have hdvd : 2 ^ n ∣ Nat.card G := hn ▸ Subgroup.card_subgroup_dvd_card P
  rw [hn]
  exact Nat.le_of_dvd (Nat.ordProj_pos _ 2)
    ((Nat.prime_two.pow_dvd_iff_dvd_ordProj Nat.card_pos.ne').1 hdvd)

theorem odd_degree_three_projective_groups_elementary_two_bound :
    (∀ (k : Type*) [Field k] [Finite k], Odd (Nat.card k) →
      ∀ A : Subgroup (projectiveSL 3 k), IsElementaryAbelian 2 A → Nat.card A ≤ 4) ∧
    (∀ (p f : ℕ) (E : Type) [Field E] (h : UnitaryFieldData p f E), p ≠ 2 →
      ∀ A : Subgroup (unitaryPSU h 3), IsElementaryAbelian 2 A → Nat.card A ≤ 4) ∧
    (∀ (p f : ℕ) (E : Type) [Field E] (h : UnitaryFieldData p f E), p ≠ 2 →
      ∀ G₀ : Matrix (Fin 3) (Fin 3) E, (∀ i j, h.bar (G₀ j i) = G₀ i j) → G₀.det ≠ 0 →
      ∀ A : Subgroup (StatedProj (SUgram h.bar G₀)), IsElementaryAbelian 2 A →
        Nat.card A ≤ 4) ∧
    (∀ (k : Type*) [Field k] [Finite k], Nat.card k = 5 →
      ordProj[2] (Nat.card (projectiveSL 3 k)) = 32 ∧
      ∀ P : Subgroup (projectiveSL 3 k), IsPGroup 2 P → Nat.card P ≤ 32) ∧
    (∀ (E : Type) [Field E] (h : UnitaryFieldData 5 1 E),
      ordProj[2] (Nat.card (unitaryPSU h 3)) = 16 ∧
      ∀ P : Subgroup (unitaryPSU h 3), IsPGroup 2 P → Nat.card P ≤ 16) := by
  have h4 : ordProj[2] (5 - 1) = 4 := by
    rw [show 5 - 1 = 2 ^ 2 by norm_num, Nat.ordProj_self_pow Nat.prime_two]
    norm_num
  have h6 : ordProj[2] (5 + 1) = 2 := by
    rw [show 5 + 1 = 2 * 3 by norm_num]
    exact ordProj_two_two_mul (by decide)
  have hunit2 : ∀ {p f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData p f E), p ≠ 2 →
      (2 : E) ≠ 0 := fun {p f E} _ h hp2 => by
    have : CharP E p := h.charP
    intro h0
    have := (CharP.cast_eq_zero_iff E p 2).1 (by exact_mod_cast h0)
    have := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this
    exact hp2 this
  refine ⟨fun k _ _ hk A hA => ?_, fun p f E _ h hp2 A hA => ?_,
    fun p f E _ h hp2 G₀ _ _ A hA => ?_, fun k _ _ hk => ?_, fun E _ h => ?_⟩
  ·
    have := Fintype.ofFinite k
    have hc : ringChar k ≠ 2 := by
      rw [Ne, FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card]
      exact Nat.odd_iff.1 hk ▸ one_ne_zero
    exact card_le_four_of_quotient (Ring.two_ne_zero hc) SpecialLinearGroup.toGL
      SpecialLinearGroup.toGL_injective (fun g => Units.ext (by
        rw [GeneralLinearGroup.val_det_apply, Units.val_one]
        exact g.2)) (Z := scalars 3 k) (fun z hz => pow_three_eq_one_of_mem_scalars hz) A
  ·
    have := h.finite
    exact card_le_four_of_quotient (hunit2 h hp2) (unitarySU p f E 3).subtype
      (unitarySU p f E 3).subtype_injective (fun g => Units.ext (by
        rw [GeneralLinearGroup.val_det_apply, Units.val_one]
        exact ((mem_unitarySU_iff h).1 g.2).1))
      (Z := unitaryScalars h 3) (fun z hz => pow_three_eq_one_of_mem_unitaryScalars h hz) A
  ·
    have := h.finite
    exact card_le_four_of_quotient (hunit2 h hp2) (SUgram h.bar G₀).subtype
      (SUgram h.bar G₀).subtype_injective (fun g => Units.ext (by
        rw [GeneralLinearGroup.val_det_apply, Units.val_one]
        exact det_eq_one_of_mem_SUgram g.2))
      (Z := (StatedScalars (Fin 3) E).subgroupOf (SUgram h.bar G₀))
      (fun z hz => pow_three_eq_one_of_mem_statedScalars (fun _ hx => det_eq_one_of_mem_SUgram hx)
        hz) A
  ·
    have hodd : Odd (Nat.card k) := by rw [hk]; decide
    have h32 : ordProj[2] (Nat.card (projectiveSL 3 k)) = 32 := by
      rw [ordProj_two_card_projectiveSL_three hodd, hk, h4, h6]
      norm_num
    exact ⟨h32, fun P hP => h32 ▸ card_le_ordProj_of_isPGroup hP⟩
  ·
    have := h.finite
    have h16 : ordProj[2] (Nat.card (unitaryPSU h 3)) = 16 := by
      rw [ordProj_two_card_unitaryPSU_three h (by norm_num), pow_one, h4, h6]
      norm_num
    exact ⟨h16, fun P hP => h16 ▸ card_le_ordProj_of_isPGroup hP⟩

end CFSG.LocalAnalysis.SteinbergCD
