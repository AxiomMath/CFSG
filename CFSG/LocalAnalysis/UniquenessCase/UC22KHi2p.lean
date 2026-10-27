module

public import CFSG.Quasithin.Background.B6Sections
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.P22k2

open CFSG.Open Subgroup CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

@[expose] def ActsOrdThree (V₀ : Subgroup G) (x : G) : Prop :=
  x ∉ centralizer (V₀ : Set G) ∧ x ^ 3 ∈ centralizer (V₀ : Set G)

structure S3Frame (P T₁ V₀ : Subgroup G) : Prop where
  le : T₁ ≤ P
  pgroup : IsPGroup 2 T₁
  odd : ¬ 2 ∣ T₁.relIndex P
  v₀le : V₀ ≤ P
  norm : P ≤ normalizer (V₀ : Set G)
  elem : IsElemAbelian 2 V₀
  card : Nat.card V₀ = 4
  act : ¬ T₁ ≤ centralizer (V₀ : Set G)
  ord3 : ∃ x ∈ P, ActsOrdThree V₀ x
  minimal : ∀ X : Subgroup G, T₁ ≤ X → X ≤ P → (∃ x ∈ X, ActsOrdThree V₀ x) → X = P
  fstar : P ⊓ centralizer (pCoreOf 2 P : Set G) ≤ pCoreOf 2 P

theorem s3_perm3_fixed : ∀ p : Equiv.Perm (Fin 3), p ^ 3 = 1 → p ≠ 1 → ∀ i, p i ≠ i := by decide

section KleinFour

open scoped IsKleinFour

variable (W : Type*) [Group W] [IsKleinFour W]

@[expose] noncomputable def s3_restrict : MulAut W →* Equiv.Perm {v : W // v ≠ 1} where
  toFun σ := Equiv.subtypeEquiv σ.toEquiv (fun v => by simp)
  map_one' := by ext; rfl
  map_mul' σ τ := by ext; rfl

theorem s3_restrict_injective : Function.Injective (s3_restrict W) := by
  intro σ τ h
  ext v
  by_cases hv : v = 1
  · simp [hv]
  · exact congrArg (fun π : Equiv.Perm {v : W // v ≠ 1} => (π ⟨v, hv⟩ : W)) h

theorem s3_restrict_surjective : Function.Surjective (s3_restrict W) := by
  classical
  intro π
  let e : W ≃ W := π.extendDomain (Equiv.refl _)
  have he1 : e 1 = 1 := Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp)
  let σ : W ≃* W := IsKleinFour.mulEquiv' e he1 IsKleinFour.exponent_two
  refine ⟨σ, ?_⟩
  ext ω
  show (e ω : W) = (π ω : W)
  exact Equiv.Perm.extendDomain_apply_subtype π (Equiv.refl _) (p := fun v : W => v ≠ 1)
    (b := ω.1) ω.2

@[expose] noncomputable def s3_autEquiv : MulAut W ≃* Equiv.Perm {v : W // v ≠ 1} :=
  MulEquiv.ofBijective (s3_restrict W) ⟨s3_restrict_injective W, s3_restrict_surjective W⟩

theorem s3_autEquiv_apply (σ : MulAut W) : s3_autEquiv W σ = s3_restrict W σ := rfl

theorem s3_card_omega : Nat.card {v : W // v ≠ 1} = 3 := by
  classical
  have h4 : Nat.card W = 4 := IsKleinFour.card_four
  haveI : Fintype W := Fintype.ofFinite W
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [Nat.card_eq_fintype_card] at h4
  omega

theorem s3_exists_equiv_perm_fin3 :
    ∃ (e : MulAut W ≃* Equiv.Perm (Fin 3)) (f : {v : W // v ≠ 1} ≃ Fin 3),
      ∀ (σ : MulAut W) (ω : {v : W // v ≠ 1}), e σ (f ω) = f (s3_restrict W σ ω) := by
  classical
  haveI : Fintype {v : W // v ≠ 1} := Fintype.ofFinite _
  have h3 : Fintype.card {v : W // v ≠ 1} = Fintype.card (Fin 3) := by
    rw [← Nat.card_eq_fintype_card, s3_card_omega]; simp
  let f : {v : W // v ≠ 1} ≃ Fin 3 := Fintype.equivOfCardEq h3
  refine ⟨(s3_autEquiv W).trans (Equiv.permCongrHom f), f, fun σ ω => ?_⟩
  simp [s3_autEquiv_apply, Equiv.permCongrHom, Equiv.permCongr_apply]

theorem s3_card_mulAut : Nat.card (MulAut W) = 6 := by
  obtain ⟨e, f, -⟩ := s3_exists_equiv_perm_fin3 W
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  rfl

theorem s3_mulAut_center (τ : MulAut W) (h : ∀ g : MulAut W, g * τ = τ * g) : τ = 1 := by
  obtain ⟨e, f, -⟩ := s3_exists_equiv_perm_fin3 W
  apply e.injective
  rw [map_one]
  refine CFSG.perm_eq_one_of_forall_commute (by simp) fun q => ?_
  have := congrArg e (h (e.symm q))
  simpa using this.symm

theorem s3_mulAut_fixed (σ : MulAut W) (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) (v : W) (hv : σ v = v) :
    v = 1 := by
  by_contra hv1
  obtain ⟨e, f, hef⟩ := s3_exists_equiv_perm_fin3 W
  refine s3_perm3_fixed (e σ) (by rw [← map_pow, h3, map_one])
    (fun h => h1 (e.injective (by rw [h, map_one]))) (f ⟨v, hv1⟩) ?_
  rw [hef]
  exact congrArg f (Subtype.ext hv)

end KleinFour

section Order6

variable {A : Type*} [Group A]

theorem s3_prime_dvd_natCard {N : Subgroup A} {σ : A} (hσ : σ ∈ N) (hσ1 : σ ≠ 1) {p k : ℕ}
    (hp : p.Prime) (hk : σ ^ p ^ k = 1) : p ∣ Nat.card N := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hσ1 (orderOf_eq_one_iff.1 (by simpa using hj))
  have : p ∣ orderOf σ := by rw [hj]; exact dvd_pow_self p hj0
  exact this.trans (Subgroup.orderOf_dvd_natCard N hσ)

theorem s3_three_dvd_natCard {N : Subgroup A} {σ : A} (hσ : σ ∈ N) (hσ1 : σ ≠ 1) (h3 : σ ^ 3 = 1) :
    3 ∣ Nat.card N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := orderOf_eq_prime h3 hσ1
  rw [← this]
  exact Subgroup.orderOf_dvd_natCard N hσ

theorem s3_finite_of_card_six (hA : Nat.card A = 6) : Finite A :=
  Nat.finite_of_card_ne_zero (by omega)

theorem s3_card_dvd_six (hA : Nat.card A = 6) (N : Subgroup A) : Nat.card N ∣ 6 :=
  hA ▸ Subgroup.card_subgroup_dvd_card N

theorem s3_eq_top_of_dvd (hA : Nat.card A = 6) {N : Subgroup A} (h2 : 2 ∣ Nat.card N)
    (h3 : 3 ∣ Nat.card N) : N = ⊤ := by
  haveI := s3_finite_of_card_six hA
  have h6 : 6 ∣ Nat.card N := by omega
  have hle : Nat.card N ≤ 6 := Nat.le_of_dvd (by norm_num) (s3_card_dvd_six hA N)
  have h7 : 6 ≤ Nat.card N := Nat.le_of_dvd Nat.card_pos h6
  exact (Subgroup.card_eq_iff_eq_top N).1 (by omega)

theorem s3_card_eq_two_of_dvd (hA : Nat.card A = 6) {N : Subgroup A} (h2 : 2 ∣ Nat.card N)
    (h3 : ¬ 3 ∣ Nat.card N) : Nat.card N = 2 := by
  have hd := s3_card_dvd_six hA N
  have hle : Nat.card N ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 0 < Nat.card N := by
    haveI := s3_finite_of_card_six hA
    exact Nat.card_pos
  interval_cases hc : Nat.card N <;> omega

theorem s3_card_le_two_of_isPGroup (hA : Nat.card A = 6) {N : Subgroup A} (hN : IsPGroup 2 N) :
    Nat.card N ≤ 2 := by
  haveI := s3_finite_of_card_six hA
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hN
  have hd := s3_card_dvd_six hA N
  rw [hn] at hd ⊢
  rcases n with _ | _ | n
  · norm_num
  · norm_num
  · exfalso
    have h4 : 4 ∣ 2 ^ (n + 2) := ⟨2 ^ n, by ring⟩
    have := h4.trans hd
    omega

theorem s3_normal_two_trivial (hA : Nat.card A = 6)
    (hZ : ∀ τ : A, (∀ g : A, g * τ = τ * g) → τ = 1) (N : Subgroup A) [hN : N.Normal]
    (h2 : ∀ n ∈ N, ∃ k : ℕ, n ^ 2 ^ k = 1) : N = ⊥ := by
  haveI := s3_finite_of_card_six hA
  have h3 : ¬ 3 ∣ Nat.card N := by
    intro h3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 h3
    obtain ⟨k, hk⟩ := h2 x x.2
    have h1 : orderOf (x : A) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    have h4 := orderOf_dvd_of_pow_eq_one hk
    rw [h1] at h4
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4
    omega
  by_contra hne
  have h1 : Nat.card N ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq N h)
  have hd := s3_card_dvd_six hA N
  have hle : Nat.card N ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hc2 : Nat.card N = 2 := by interval_cases hc : Nat.card N <;> omega
  obtain ⟨n, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  obtain ⟨y, -, hyu⟩ := (Nat.card_eq_two_iff' (1 : N)).1 hc2
  have hcentral : ∀ g : A, g * (n : A) = (n : A) * g := by
    intro g
    have hmem : g * (n : A) * g⁻¹ ∈ N := hN.conj_mem n n.2 g
    have hne1 : (⟨g * (n : A) * g⁻¹, hmem⟩ : N) ≠ 1 := by
      intro h
      apply hn1
      have h' : g * (n : A) * g⁻¹ = 1 := congrArg Subtype.val h
      have : (n : A) = 1 := by simpa using h'
      exact Subtype.ext this
    have heq : (⟨g * (n : A) * g⁻¹, hmem⟩ : N) = n := (hyu _ hne1).trans (hyu _ hn1).symm
    have := congrArg Subtype.val heq
    exact (mul_inv_eq_iff_eq_mul.1 this)
  exact hn1 (Subtype.ext (hZ n hcentral))

end Order6

section Psi

variable {P V₀ : Subgroup G}

@[expose] noncomputable def s3_psi (hP : P ≤ normalizer (V₀ : Set G)) : ↥P →* MulAut ↥V₀ :=
  (normalizerMonoidHom V₀).comp (Subgroup.inclusion hP)

theorem s3_psi_coe (hP : P ≤ normalizer (V₀ : Set G)) (p : ↥P) (v : ↥V₀) :
    ((s3_psi hP p v : ↥V₀) : G) = (p : G) * (v : G) * (p : G)⁻¹ := rfl

theorem s3_psi_eq_one_iff (hP : P ≤ normalizer (V₀ : Set G)) (p : ↥P) :
    s3_psi hP p = 1 ↔ (p : G) ∈ centralizer (V₀ : Set G) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h v hv
    have := congrArg (fun σ : MulAut ↥V₀ => ((σ ⟨v, hv⟩ : ↥V₀) : G)) h
    simp only [s3_psi_coe, MulAut.one_apply] at this
    calc v * p = (p * v * (p : G)⁻¹) * p := by rw [this]
      _ = p * v := by group
  · intro h
    ext v
    simp only [s3_psi_coe, MulAut.one_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact (h v v.2).symm

theorem s3_psi_mk_eq_one_iff (hP : P ≤ normalizer (V₀ : Set G)) {x : G} (hx : x ∈ P) :
    s3_psi hP ⟨x, hx⟩ = 1 ↔ x ∈ centralizer (V₀ : Set G) :=
  s3_psi_eq_one_iff hP ⟨x, hx⟩

theorem s3_psi_mk_pow (hP : P ≤ normalizer (V₀ : Set G)) {x : G} (hx : x ∈ P) (n : ℕ) :
    s3_psi hP ⟨x, hx⟩ ^ n = s3_psi hP ⟨x ^ n, P.pow_mem hx n⟩ := by
  rw [← map_pow]
  rfl

@[expose] noncomputable def s3_img (hP : P ≤ normalizer (V₀ : Set G)) (X : Subgroup G) :
    Subgroup (MulAut ↥V₀) :=
  (X.subgroupOf P).map (s3_psi hP)

theorem s3_mem_img {hP : P ≤ normalizer (V₀ : Set G)} {X : Subgroup G} {σ : MulAut ↥V₀} :
    σ ∈ s3_img hP X ↔ ∃ x : ↥P, (x : G) ∈ X ∧ s3_psi hP x = σ := by
  simp [s3_img, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem s3_psi_mem_img {hP : P ≤ normalizer (V₀ : Set G)} {X : Subgroup G} {x : G} (hxP : x ∈ P)
    (hxX : x ∈ X) : s3_psi hP ⟨x, hxP⟩ ∈ s3_img hP X :=
  s3_mem_img.2 ⟨⟨x, hxP⟩, hxX, rfl⟩

theorem s3_img_mono {hP : P ≤ normalizer (V₀ : Set G)} {X Y : Subgroup G} (hXY : X ≤ Y) :
    s3_img hP X ≤ s3_img hP Y := fun _ hσ => by
  obtain ⟨x, hx, rfl⟩ := s3_mem_img.1 hσ
  exact s3_mem_img.2 ⟨x, hXY hx, rfl⟩

end Psi

theorem s3_exists_pow_eq_one {T : Subgroup G} (hT : IsPGroup 2 T) {t : G} (ht : t ∈ T) :
    ∃ k : ℕ, t ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

namespace S3Frame

variable {P T₁ V₀ : Subgroup G} (h : S3Frame P T₁ V₀)

include h

theorem s3_isKleinFour : IsKleinFour ↥V₀ where
  card_four := h.card
  exponent_two := by
    haveI : Nontrivial ↥V₀ := Finite.one_lt_card_iff_nontrivial.1 (by rw [h.card]; norm_num)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine (Monoid.exponent_eq_prime_iff Nat.prime_two).2 fun g hg => ?_
    refine orderOf_eq_prime ?_ hg
    apply Subtype.ext
    simpa using h.elem.2 g g.2

theorem s3_card_aut : Nat.card (MulAut ↥V₀) = 6 := by
  haveI := h.s3_isKleinFour
  exact s3_card_mulAut ↥V₀

theorem s3_aut_center (τ : MulAut ↥V₀) (hτ : ∀ g : MulAut ↥V₀, g * τ = τ * g) : τ = 1 := by
  haveI := h.s3_isKleinFour
  exact s3_mulAut_center ↥V₀ τ hτ

theorem s3_psi_ne_one_of_acts {x : G} (hx : x ∈ P) (hact : ActsOrdThree V₀ x) :
    s3_psi h.norm ⟨x, hx⟩ ≠ 1 := fun h1 =>
  hact.1 ((s3_psi_mk_eq_one_iff h.norm hx).1 h1)

theorem s3_psi_pow_three_of_acts {x : G} (hx : x ∈ P) (hact : ActsOrdThree V₀ x) :
    s3_psi h.norm ⟨x, hx⟩ ^ 3 = 1 := by
  rw [s3_psi_mk_pow]
  exact (s3_psi_mk_eq_one_iff h.norm _).2 hact.2

theorem s3_psi_surjective : Function.Surjective (s3_psi h.norm) := by
  have hA := h.s3_card_aut
  obtain ⟨x, hxP, hxact⟩ := h.ord3
  obtain ⟨t, htT, htC⟩ := SetLike.not_le_iff_exists.1 h.act
  have h3 : 3 ∣ Nat.card (s3_psi h.norm).range :=
    s3_three_dvd_natCard (N := (s3_psi h.norm).range) (σ := s3_psi h.norm ⟨x, hxP⟩)
      (MonoidHom.mem_range.2 ⟨_, rfl⟩) (h.s3_psi_ne_one_of_acts hxP hxact)
      (h.s3_psi_pow_three_of_acts hxP hxact)
  have h2 : 2 ∣ Nat.card (s3_psi h.norm).range := by
    obtain ⟨k, hk⟩ := s3_exists_pow_eq_one h.pgroup htT
    refine s3_prime_dvd_natCard (N := (s3_psi h.norm).range) (σ := s3_psi h.norm ⟨t, h.le htT⟩)
      (MonoidHom.mem_range.2 ⟨_, rfl⟩) ?_ Nat.prime_two (k := k) ?_
    · exact fun h1 => htC ((s3_psi_mk_eq_one_iff h.norm _).1 h1)
    · rw [s3_psi_mk_pow]
      exact (s3_psi_mk_eq_one_iff h.norm _).2 (by simp [hk])
  exact MonoidHom.range_eq_top.1 (s3_eq_top_of_dvd hA h2 h3)

theorem s3_le_normalizer_ker :
    P ≤ normalizer ((P ⊓ centralizer (V₀ : Set G) : Subgroup G) : Set G) := fun g hg =>
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hg, B6.le_normalizer_centralizer h.norm hg⟩

theorem s3_isPGroup_img_T₁ : IsPGroup 2 (s3_img h.norm T₁) := by
  intro σ
  obtain ⟨x, hxT, hxσ⟩ := s3_mem_img.1 σ.2
  obtain ⟨k, hk⟩ := s3_exists_pow_eq_one h.pgroup hxT
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hxσ, ← map_pow]
  exact (s3_psi_eq_one_iff h.norm _).2 (by simp [hk])

theorem s3_card_img_T₁ : Nat.card (s3_img h.norm T₁) = 2 := by
  have hA := h.s3_card_aut
  obtain ⟨t, htT, htC⟩ := SetLike.not_le_iff_exists.1 h.act
  have h2 : 2 ∣ Nat.card (s3_img h.norm T₁) := by
    obtain ⟨k, hk⟩ := s3_exists_pow_eq_one h.pgroup htT
    refine s3_prime_dvd_natCard (N := s3_img h.norm T₁) (σ := s3_psi h.norm ⟨t, h.le htT⟩)
      (s3_psi_mem_img (h.le htT) htT) ?_ Nat.prime_two (k := k) ?_
    · exact fun h1 => htC ((s3_psi_mk_eq_one_iff h.norm _).1 h1)
    · rw [s3_psi_mk_pow]
      exact (s3_psi_mk_eq_one_iff h.norm _).2 (by simp [hk])
  have hle := s3_card_le_two_of_isPGroup hA h.s3_isPGroup_img_T₁
  haveI := s3_finite_of_card_six hA
  have hpos : 0 < Nat.card (s3_img h.norm T₁) := Nat.card_pos
  have := Nat.le_of_dvd hpos h2
  omega

theorem s3_exists_actsOrdThree_of_three_dvd {X : Subgroup G}
    (h3 : 3 ∣ Nat.card (s3_img h.norm X)) : ∃ x ∈ X, ActsOrdThree V₀ x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := s3_finite_of_card_six h.s3_card_aut
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := s3_img h.norm X) 3 h3
  obtain ⟨x, hxX, hxσ⟩ := s3_mem_img.1 σ.2
  have hord : orderOf (σ : MulAut ↥V₀) = 3 := by rw [Subgroup.orderOf_coe]; exact hσ
  refine ⟨(x : G), hxX, ?_, ?_⟩
  · intro hxC
    have h1 : s3_psi h.norm x = 1 := (s3_psi_eq_one_iff h.norm x).2 hxC
    rw [hxσ] at h1
    rw [h1, orderOf_one] at hord
    omega
  · have h1 : (σ : MulAut ↥V₀) ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    rw [← hxσ, ← map_pow] at h1
    exact (s3_psi_eq_one_iff h.norm _).1 h1

theorem s3_le_sup_of_img_le {X : Subgroup G} (hXP : X ≤ P)
    (hX : s3_img h.norm X ≤ s3_img h.norm T₁) : X ≤ (P ⊓ centralizer (V₀ : Set G)) ⊔ T₁ := by
  intro x hx
  have hxP : x ∈ P := hXP hx
  obtain ⟨t, htT, hteq⟩ := s3_mem_img.1 (hX (s3_psi_mem_img hxP hx))
  have hk : x * (t : G)⁻¹ ∈ P ⊓ centralizer (V₀ : Set G) := by
    refine ⟨P.mul_mem hxP (P.inv_mem t.2), ?_⟩
    have h1 : s3_psi h.norm (⟨x, hxP⟩ * t⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hteq, mul_inv_cancel]
    exact (s3_psi_eq_one_iff h.norm _).1 h1
  have hx' : x = (x * (t : G)⁻¹) * t := by group
  rw [hx']
  exact Subgroup.mul_mem_sup hk htT

theorem s3_img_ker_sup_le :
    s3_img h.norm ((P ⊓ centralizer (V₀ : Set G)) ⊔ T₁) ≤ s3_img h.norm T₁ := by
  intro σ hσ
  obtain ⟨m, hm, rfl⟩ := s3_mem_img.1 hσ
  have hT : T₁ ≤ normalizer ((P ⊓ centralizer (V₀ : Set G) : Subgroup G) : Set G) :=
    h.le.trans h.s3_le_normalizer_ker
  have hm' := hm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hT] at hm'
  obtain ⟨k, hk, t, ht, hkt⟩ := hm'
  have hmP : (m : G) = k * t := hkt.symm
  have e : m = ⟨k, hk.1⟩ * ⟨t, h.le ht⟩ := Subtype.ext hmP
  refine s3_mem_img.2 ⟨⟨t, h.le ht⟩, ht, ?_⟩
  rw [e, map_mul]
  have : s3_psi h.norm ⟨k, hk.1⟩ = 1 := (s3_psi_eq_one_iff h.norm _).2 hk.2
  rw [this, one_mul]

theorem s3_exists_pow_mem_centralizer {x : G} (hxP : x ∈ P)
    (hx : x ∈ (P ⊓ centralizer (V₀ : Set G)) ⊔ T₁) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ centralizer (V₀ : Set G) := by
  have hσ : s3_psi h.norm ⟨x, hxP⟩ ∈ s3_img h.norm T₁ :=
    h.s3_img_ker_sup_le (s3_psi_mem_img hxP hx)
  obtain ⟨k, hk⟩ := h.s3_isPGroup_img_T₁ ⟨_, hσ⟩
  refine ⟨k, ?_⟩
  have h1 : s3_psi h.norm ⟨x, hxP⟩ ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [s3_psi_mk_pow] at h1
  exact (s3_psi_mk_eq_one_iff h.norm _).1 h1

end S3Frame

theorem S3Frame.isTwoReduced {P T₁ V₀ : Subgroup G} (h : S3Frame P T₁ V₀) : IsTwoReducedIn P V₀ := by
  refine ⟨h.v₀le, h.norm, h.elem, fun D hDP hDn hD2 => ?_⟩
  have hsurj := h.s3_psi_surjective
  haveI hNormal : (s3_img h.norm D).Normal := by
    refine ⟨fun σ hσ g => ?_⟩
    obtain ⟨d, hd, rfl⟩ := s3_mem_img.1 hσ
    obtain ⟨p, rfl⟩ := hsurj g
    refine s3_mem_img.2 ⟨p * d * p⁻¹, ?_, by simp [map_mul, map_inv]⟩
    exact (mem_normalizer_iff.1 (hDn p.2) d).1 hd
  have hbot : s3_img h.norm D = ⊥ := by
    refine s3_normal_two_trivial h.s3_card_aut h.s3_aut_center _ ?_
    intro σ hσ
    obtain ⟨d, hd, rfl⟩ := s3_mem_img.1 hσ
    obtain ⟨k, hk⟩ := hD2 d hd
    refine ⟨k, ?_⟩
    rw [← map_pow]
    exact (s3_psi_eq_one_iff h.norm _).2 (by simpa using hk)
  intro d hd
  have h1 : s3_psi h.norm ⟨d, hDP hd⟩ ∈ s3_img h.norm D := s3_psi_mem_img (hDP hd) hd
  rw [hbot, Subgroup.mem_bot] at h1
  exact (s3_psi_mk_eq_one_iff h.norm _).1 h1

theorem S3Frame.minParabolic {P T₁ V₀ : Subgroup G} (h : S3Frame P T₁ V₀) :
    MinParabolic P T₁ ((P ⊓ centralizer (V₀ : Set G)) ⊔ T₁) := by
  have hA := h.s3_card_aut
  have hred := h.isTwoReduced
  have hMP : (P ⊓ centralizer (V₀ : Set G)) ⊔ T₁ ≤ P := sup_le inf_le_left h.le
  have hT2 := h.s3_card_img_T₁
  have hTM : T₁ ≤ (P ⊓ centralizer (V₀ : Set G)) ⊔ T₁ := le_sup_right
  have hMlt : (P ⊓ centralizer (V₀ : Set G)) ⊔ T₁ < P := by
    refine lt_of_le_of_ne hMP fun hEq => ?_
    obtain ⟨x, hxP, hxact⟩ := h.ord3
    have hxM : x ∈ (P ⊓ centralizer (V₀ : Set G)) ⊔ T₁ := by rw [hEq]; exact hxP
    have h3 := s3_three_dvd_natCard (N := s3_img h.norm T₁) (σ := s3_psi h.norm ⟨x, hxP⟩)
      (h.s3_img_ker_sup_le (s3_psi_mem_img hxP hxM)) (h.s3_psi_ne_one_of_acts hxP hxact)
      (h.s3_psi_pow_three_of_acts hxP hxact)
    rw [hT2] at h3
    omega
  refine ⟨⟨h.le, h.pgroup, h.odd⟩, ?_, ?_⟩
  · intro hn
    apply h.act
    refine hred.2.2.2 T₁ h.le hn (fun d hd => ?_)
    obtain ⟨k, hk⟩ := s3_exists_pow_eq_one h.pgroup hd
    exact ⟨k, by rw [hk]; exact one_mem _⟩
  · rw [isUniqueMaxOver_iff]
    refine ⟨⟨hMlt, fun Y hMY hYP => ?_⟩, hTM, fun N hN hTN => ?_⟩
    ·
      have hTY : T₁ ≤ Y := hTM.trans hMY.le
      have hTYimg : s3_img h.norm T₁ ≤ s3_img h.norm Y := s3_img_mono hTY
      have h2 : 2 ∣ Nat.card (s3_img h.norm Y) := by
        rw [← hT2]; exact Subgroup.card_dvd_of_le hTYimg
      have hnle : ¬ s3_img h.norm Y ≤ s3_img h.norm T₁ := fun hle =>
        absurd (h.s3_le_sup_of_img_le hYP hle) (not_le_of_gt hMY)
      have h3 : 3 ∣ Nat.card (s3_img h.norm Y) := by
        by_contra h3
        have := s3_card_eq_two_of_dvd hA h2 h3
        apply hnle
        have heq : s3_img h.norm T₁ = s3_img h.norm Y := by
          haveI := s3_finite_of_card_six hA
          exact Subgroup.eq_of_le_of_card_ge hTYimg (by omega)
        exact heq.symm.le
      obtain ⟨x, hxY, hxact⟩ := h.s3_exists_actsOrdThree_of_three_dvd h3
      exact h.minimal Y hTY hYP ⟨x, hxY, hxact⟩
    ·
      obtain ⟨hNlt, hNmax⟩ := hN
      have hNP : N ≤ P := hNlt.le
      have h3 : ¬ 3 ∣ Nat.card (s3_img h.norm N) := fun h3 => by
        obtain ⟨x, hxN, hxact⟩ := h.s3_exists_actsOrdThree_of_three_dvd h3
        exact absurd (h.minimal N hTN hNP ⟨x, hxN, hxact⟩) (ne_of_lt hNlt)
      have hTNimg : s3_img h.norm T₁ ≤ s3_img h.norm N := s3_img_mono hTN
      have h2 : 2 ∣ Nat.card (s3_img h.norm N) := by
        rw [← hT2]; exact Subgroup.card_dvd_of_le hTNimg
      have hc := s3_card_eq_two_of_dvd hA h2 h3
      have hNle : N ≤ (P ⊓ centralizer (V₀ : Set G)) ⊔ T₁ := by
        refine h.s3_le_sup_of_img_le hNP ?_
        haveI := s3_finite_of_card_six hA
        exact (Subgroup.eq_of_le_of_card_ge hTNimg (by omega)).symm.le
      by_contra hne
      exact absurd (hNmax _ (lt_of_le_of_ne hNle hne) hMP) (ne_of_lt hMlt)

theorem S3Frame.kerIn_eq {P T₁ V₀ : Subgroup G} (h : S3Frame P T₁ V₀) :
    kerIn ((P ⊓ centralizer (V₀ : Set G)) ⊔ T₁) P = P ⊓ centralizer (V₀ : Set G) := by
  apply le_antisymm
  · intro x hx
    have hxP : x ∈ P := h.minParabolic.kerIn_le_H hx
    refine ⟨hxP, ?_⟩
    refine h.isTwoReduced.2.2.2 (kerIn ((P ⊓ centralizer (V₀ : Set G)) ⊔ T₁) P)
      h.minParabolic.kerIn_le_H (le_normalizer_kerIn _ _) (fun d hd => ?_) hx
    exact h.s3_exists_pow_mem_centralizer (h.minParabolic.kerIn_le_H hd) (kerIn_le hd)
  · exact le_kerIn_of_le_normalizer le_sup_left h.s3_le_normalizer_ker

section Normal

open CFSG.LieType.BorelTits

theorem s3_pCoreOf_eq_inf {P H : Subgroup G} (hHP : H ≤ P) (hHn : P ≤ normalizer (H : Set G)) :
    pCoreOf 2 H = H ⊓ pCoreOf 2 P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine le_inf (pCoreOf_le 2 H) ?_
    exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 H).trans hHP)
      (hHn.trans (normalizer_le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  · refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 P).to_le inf_le_right)
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, le_normalizer_pCoreOf 2 P (hHP hg)⟩

theorem s3_conj_eq_of_commute_commutator {y q : G} {r : ℕ} (hr : Odd r) (hy : y ^ r = 1)
    (hc2 : ∃ b : ℕ, (y * q * y⁻¹ * q⁻¹) ^ (2 ^ b) = 1)
    (hcomm : y * (y * q * y⁻¹ * q⁻¹) = (y * q * y⁻¹ * q⁻¹) * y) : y * q * y⁻¹ = q := by
  set c := y * q * y⁻¹ * q⁻¹ with hc
  have hyc : y * c * y⁻¹ = c := by rw [hcomm]; group
  have hyck : ∀ k : ℕ, y * c ^ k * y⁻¹ = c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc y * c ^ (k + 1) * y⁻¹ = (y * c ^ k * y⁻¹) * (y * c * y⁻¹) := by rw [pow_succ]; group
        _ = c ^ (k + 1) := by rw [ih, hyc, pow_succ]
  have hpow : ∀ k : ℕ, y ^ k * q * (y ^ k)⁻¹ = c ^ k * q := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc y ^ (k + 1) * q * (y ^ (k + 1))⁻¹ = y * (y ^ k * q * (y ^ k)⁻¹) * y⁻¹ := by
            rw [pow_succ']; group
        _ = (y * c ^ k * y⁻¹) * (y * q * y⁻¹) := by rw [ih]; group
        _ = c ^ k * (c * q) := by rw [hyck k, hc]; group
        _ = c ^ (k + 1) * q := by rw [pow_succ]; group
  have hcr : c ^ r = 1 := by
    have h1 := hpow r
    rw [hy] at h1
    have : q = c ^ r * q := by simpa using h1
    have h2 := congrArg (fun z => z * q⁻¹) this
    simpa using h2.symm
  obtain ⟨b, hb⟩ := hc2
  have hdvd1 : orderOf c ∣ r := orderOf_dvd_of_pow_eq_one hcr
  have hdvd2 : orderOf c ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one hb
  have hcop : Nat.Coprime r (2 ^ b) := Nat.Coprime.pow_right b ((Nat.coprime_two_right).2 hr)
  have h1 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have hc1 : c = 1 := orderOf_eq_one_iff.1 h1
  have : y * q * y⁻¹ * q⁻¹ * q = q := by rw [← hc, hc1, one_mul]
  simpa using this

theorem s3_eq_one_of_odd_of_isPGroup {Q : Subgroup G} (hQ : IsPGroup 2 Q) {y : G} (hyQ : y ∈ Q)
    {r : ℕ} (hr : Odd r) (hyr : y ^ r = 1) : y = 1 := by
  obtain ⟨b, hb⟩ := s3_exists_pow_eq_one hQ hyQ
  have hcop : Nat.Coprime r (2 ^ b) := Nat.Coprime.pow_right b ((Nat.coprime_two_right).2 hr)
  exact orderOf_eq_one_iff.1
    (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hyr) (orderOf_dvd_of_pow_eq_one hb))

theorem s3_fstar_of_normal {P H : Subgroup G} (hHP : H ≤ P) (hHn : P ≤ normalizer (H : Set G))
    (hF : P ⊓ centralizer (pCoreOf 2 P : Set G) ≤ pCoreOf 2 P) :
    H ⊓ centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRe := s3_pCoreOf_eq_inf hHP hHn
  have hQ2 : IsPGroup 2 (pCoreOf 2 P) := pCoreOf_isPGroup 2 P
  have hQn : P ≤ normalizer (pCoreOf 2 P : Set G) := le_normalizer_pCoreOf 2 P
  have h2 : IsPGroup 2 ↥(H ⊓ centralizer (pCoreOf 2 H : Set G)) := by
    rintro ⟨x, hxH, hxC⟩
    obtain ⟨e, r, hr, hor⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    set y : G := x ^ 2 ^ e with hydef
    have hyr : y ^ r = 1 := by rw [hydef, ← pow_mul, ← hor, pow_orderOf_eq_one]
    have hyH : y ∈ H := H.pow_mem hxH _
    have hyC : y ∈ centralizer (pCoreOf 2 H : Set G) := (centralizer _).pow_mem hxC _
    have hyQ : ∀ q ∈ pCoreOf 2 P, y * q * y⁻¹ = q := by
      intro q hq
      have hcQ : y * q * y⁻¹ * q⁻¹ ∈ pCoreOf 2 P :=
        (pCoreOf 2 P).mul_mem ((mem_normalizer_iff.1 (hQn (hHP hyH)) q).1 hq)
          ((pCoreOf 2 P).inv_mem hq)
      have hcH : y * q * y⁻¹ * q⁻¹ ∈ H := by
        have h1 : q * y⁻¹ * q⁻¹ ∈ H :=
          (mem_normalizer_iff.1 (hHn (pCoreOf_le 2 P hq)) y⁻¹).1 (H.inv_mem hyH)
        simpa [mul_assoc] using H.mul_mem hyH h1
      have hcR : y * q * y⁻¹ * q⁻¹ ∈ pCoreOf 2 H := by rw [hRe]; exact ⟨hcH, hcQ⟩
      have hcomm := (mem_centralizer_iff.1 hyC) _ hcR
      have hc2 : ∃ b : ℕ, (y * q * y⁻¹ * q⁻¹) ^ 2 ^ b = 1 := s3_exists_pow_eq_one hQ2 hcQ
      exact s3_conj_eq_of_commute_commutator hr hyr hc2 hcomm.symm
    have hyCQ : y ∈ centralizer (pCoreOf 2 P : Set G) := by
      rw [mem_centralizer_iff]
      intro q hq
      calc q * y = (y * q * y⁻¹) * y := by rw [hyQ q hq]
        _ = y * q := by group
    have hy1 : y = 1 :=
      s3_eq_one_of_odd_of_isPGroup hQ2 (hF ⟨hHP hyH, hyCQ⟩) hr hyr
    exact ⟨e, Subtype.ext (by simpa [← hydef] using hy1)⟩
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun g hg => ?_) h2
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hg, B6.le_normalizer_centralizer (le_normalizer_pCoreOf 2 H) hg⟩

end Normal

section Frattini

theorem s3_frattini_step {X : Type*} [Group X] [Finite X] (Y J : Subgroup X)
    (hQY : CFSG.Open.pCore 2 X ≤ Y)
    (hJ : J.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) ≤ frattini (X ⧸ CFSG.Open.pCore 2 X))
    (hYJ : Y ⊔ J = ⊤) : Y = ⊤ := by
  set φ := QuotientGroup.mk' (CFSG.Open.pCore 2 X) with hφdef
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have h1 : Y.map φ ⊔ frattini (X ⧸ CFSG.Open.pCore 2 X) = ⊤ := by
    refine top_le_iff.1 ?_
    calc (⊤ : Subgroup (X ⧸ CFSG.Open.pCore 2 X)) = (Y ⊔ J).map φ := by
          rw [hYJ, Subgroup.map_top, MonoidHom.range_eq_top.2 hφ]
      _ = Y.map φ ⊔ J.map φ := Subgroup.map_sup _ _ _
      _ ≤ Y.map φ ⊔ frattini (X ⧸ CFSG.Open.pCore 2 X) := sup_le_sup_left hJ _
  have h2 : Y.map φ = ⊤ := frattini_nongenerating h1
  have h3 : Y ⊔ φ.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, h2, Subgroup.comap_top]
  rw [hφdef, QuotientGroup.ker_mk', sup_eq_left.2 hQY] at h3
  exact h3

end Frattini

@[expose] def hGen (P S : Subgroup G) : Subgroup G :=
  ⨆ l ∈ twoResidual P, S.map (MulAut.conj l).toMonoidHom

section HGen

variable {P T₁ S : Subgroup G}

theorem s3_hGen_eq_iSup (P S : Subgroup G) :
    hGen P S = ⨆ l ∈ twoResidual P, B6.conjSub l S := rfl

theorem s3_le_hGen (P S : Subgroup G) : S ≤ hGen P S := by
  rw [s3_hGen_eq_iSup]
  refine le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) ?_
  rw [B6.conjSub_one]

theorem s3_hGen_le_of_le (hSP : S ≤ P) : hGen P S ≤ P := by
  rw [s3_hGen_eq_iSup]
  refine iSup₂_le fun l hl x hx => ?_
  rw [B6.mem_conjSub] at hx
  have hlP : l ∈ P := twoResidual_le P hl
  have := P.mul_mem (P.mul_mem hlP (hSP hx)) (P.inv_mem hlP)
  simpa [mul_assoc] using this

theorem s3_conjSub_hGen_le {g : G}
    (hg : ∀ l ∈ twoResidual P, ∃ l' ∈ twoResidual P,
      B6.conjSub (g * l) S ≤ B6.conjSub l' S) :
    B6.conjSub g (hGen P S) ≤ hGen P S := by
  rw [s3_hGen_eq_iSup]
  simp only [OrderIso.map_iSup]
  refine iSup₂_le fun l hl => ?_
  obtain ⟨l', hl', hle⟩ := hg l hl
  rw [← B6.conjSub_mul]
  exact hle.trans (le_iSup₂ (f := fun l (_ : l ∈ twoResidual P) => B6.conjSub l S) l' hl')

theorem s3_conjSub_hGen_le_of_mem_T (hTP : T₁ ≤ P) (hSn : T₁ ≤ normalizer (S : Set G)) {t : G}
    (ht : t ∈ T₁) : B6.conjSub t (hGen P S) ≤ hGen P S := by
  refine s3_conjSub_hGen_le (P := P) (S := S) (g := t) ?_
  intro l hl
  have hl' : t * l * t⁻¹ ∈ twoResidual P :=
    (mem_normalizer_iff.1 (le_normalizer_twoResidual P (hTP ht)) l).1 hl
  have e : B6.conjSub (t * l) S = B6.conjSub (t * l * t⁻¹) S := by
    have e0 : t * l = (t * l * t⁻¹) * t := by group
    conv_lhs => rw [e0]
    rw [B6.conjSub_mul, B6.conjSub_eq_self (hSn ht)]
  exact ⟨t * l * t⁻¹, hl', le_of_eq e⟩

theorem s3_conjSub_hGen_le_of_mem_L {g : G} (hg : g ∈ twoResidual P) :
    B6.conjSub g (hGen P S) ≤ hGen P S := by
  refine s3_conjSub_hGen_le (P := P) (S := S) (g := g) ?_
  intro l hl
  exact ⟨g * l, (twoResidual P).mul_mem hg hl, le_rfl⟩

theorem s3_le_normalizer_hGen_of_sup_eq (hTP : T₁ ≤ P) (hSn : T₁ ≤ normalizer (S : Set G))
    (hP : T₁ ⊔ twoResidual P = P) : P ≤ normalizer (hGen P S : Set G) := by
  refine hP.symm.le.trans (sup_le (fun t ht => ?_) (fun g hg => ?_))
  · exact B6.mem_normalizer_of_conjSub_le (s3_conjSub_hGen_le_of_mem_T hTP hSn ht)
      (s3_conjSub_hGen_le_of_mem_T hTP hSn (T₁.inv_mem ht))
  · exact B6.mem_normalizer_of_conjSub_le (s3_conjSub_hGen_le_of_mem_L hg)
      (s3_conjSub_hGen_le_of_mem_L ((twoResidual P).inv_mem hg))

end HGen

section Commutator

open scoped IsMulCommutative in
theorem s3_map_surjective {W : Type*} [Group W] [Finite W] [IsMulCommutative W] (σ : MulAut W)
    (hfix : ∀ v : W, σ v = v → v = 1) : Function.Surjective (fun w : W => w * (σ w)⁻¹) := by
  refine Finite.injective_iff_surjective.1 ?_
  intro a b hab
  have h1 : a / σ a = b / σ b := by simpa [div_eq_mul_inv] using hab
  have h2 : a / b = σ a / σ b := div_eq_div_iff_div_eq_div.1 h1
  have key : σ (a / b) = a / b := by rw [map_div, ← h2]
  exact div_eq_one.1 (hfix _ key)

end Commutator

namespace S3Frame

variable {P T₁ V₀ S : Subgroup G} (h : S3Frame P T₁ V₀)

include h

theorem s3_exists_twoResidual_actsOrdThree : ∃ y ∈ twoResidual P, ActsOrdThree V₀ y := by
  obtain ⟨x, hxP, hxact⟩ := h.ord3
  obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient P x hxP
  refine ⟨x ^ 2 ^ k, hk, ?_, ?_⟩
  · intro hC
    have h1 : s3_psi h.norm ⟨x, hxP⟩ ^ 2 ^ k = 1 := by
      rw [s3_psi_mk_pow]
      exact (s3_psi_mk_eq_one_iff h.norm _).2 hC
    have h3 := orderOf_dvd_of_pow_eq_one h1
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [orderOf_eq_prime (h.s3_psi_pow_three_of_acts hxP hxact) (h.s3_psi_ne_one_of_acts hxP hxact)]
      at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  · have e : (x ^ 2 ^ k) ^ 3 = (x ^ 3) ^ 2 ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [e]
    exact (centralizer (V₀ : Set G)).pow_mem hxact.2 _

theorem s3_le_twoResidual : V₀ ≤ twoResidual P := by
  haveI := h.s3_isKleinFour
  haveI : IsMulCommutative ↥V₀ := h.elem.1
  obtain ⟨y, hyL, hyact⟩ := h.s3_exists_twoResidual_actsOrdThree
  have hyP : y ∈ P := twoResidual_le P hyL
  have hfix := s3_mulAut_fixed ↥V₀ (s3_psi h.norm ⟨y, hyP⟩) (h.s3_psi_pow_three_of_acts hyP hyact)
    (h.s3_psi_ne_one_of_acts hyP hyact)
  intro v hv
  obtain ⟨w, hw⟩ := s3_map_surjective (s3_psi h.norm ⟨y, hyP⟩) hfix ⟨v, hv⟩
  have hv' : v = (w : G) * (y * (w : G) * y⁻¹)⁻¹ := by
    have := congrArg Subtype.val hw
    simpa [s3_psi_coe] using this.symm
  have hwP : (w : G) ∈ P := h.v₀le w.2
  have h1 : (w : G) * y * (w : G)⁻¹ ∈ twoResidual P :=
    (mem_normalizer_iff.1 (le_normalizer_twoResidual P hwP) y).1 hyL
  have e : v = ((w : G) * y * (w : G)⁻¹) * y⁻¹ := by rw [hv']; group
  rw [e]
  exact (twoResidual P).mul_mem h1 ((twoResidual P).inv_mem hyL)

theorem s3_hGen_le (hS : S ≤ T₁) : hGen P S ≤ P := s3_hGen_le_of_le (hS.trans h.le)

theorem s3_le_normalizer_hGen (hSn : T₁ ≤ normalizer (S : Set G)) :
    P ≤ normalizer (hGen P S : Set G) :=
  s3_le_normalizer_hGen_of_sup_eq h.le hSn (sup_twoResidual_eq h.minParabolic.isSylow)

theorem s3_twoResidual_le_hGen (hS : S ≤ T₁) (hSn : T₁ ≤ normalizer (S : Set G))
    (hSact : ¬ S ≤ centralizer (V₀ : Set G)) : twoResidual P ≤ hGen P S := by
  rcases h.minParabolic.le_kerIn_or_twoResidual_le (h.s3_hGen_le hS) (h.s3_le_normalizer_hGen hSn)
    with hk | hk
  · exfalso
    rw [h.kerIn_eq] at hk
    exact hSact ((s3_le_hGen P S).trans hk |>.trans inf_le_right)
  · exact hk

theorem s3_img_eq_top {X : Subgroup G} (hS : S ≤ T₁) (hSact : ¬ S ≤ centralizer (V₀ : Set G))
    (hSX : S ≤ X) (hLX : twoResidual P ≤ X) : s3_img h.norm X = ⊤ := by
  obtain ⟨s, hsS, hsC⟩ := SetLike.not_le_iff_exists.1 hSact
  obtain ⟨y, hyL, hyact⟩ := h.s3_exists_twoResidual_actsOrdThree
  have hyP := twoResidual_le P hyL
  have h3 : 3 ∣ Nat.card (s3_img h.norm X) :=
    s3_three_dvd_natCard (N := s3_img h.norm X) (σ := s3_psi h.norm ⟨y, hyP⟩)
      (s3_psi_mem_img hyP (hLX hyL)) (h.s3_psi_ne_one_of_acts hyP hyact)
      (h.s3_psi_pow_three_of_acts hyP hyact)
  have h2 : 2 ∣ Nat.card (s3_img h.norm X) := by
    obtain ⟨k, hk⟩ := s3_exists_pow_eq_one h.pgroup (hS hsS)
    refine s3_prime_dvd_natCard (N := s3_img h.norm X)
      (σ := s3_psi h.norm ⟨s, h.le (hS hsS)⟩) (s3_psi_mem_img _ (hSX hsS)) ?_ Nat.prime_two
      (k := k) ?_
    · exact fun h1 => hsC ((s3_psi_mk_eq_one_iff h.norm _).1 h1)
    · rw [s3_psi_mk_pow]
      exact (s3_psi_mk_eq_one_iff h.norm _).2 (by simp [hk])
  exact s3_eq_top_of_dvd h.s3_card_aut h2 h3

theorem s3_sup_ker_eq_of_img_eq_top {Y : Subgroup G} (hYP : Y ≤ P) (hY : s3_img h.norm Y = ⊤) :
    Y ⊔ (P ⊓ centralizer (V₀ : Set G)) = P := by
  refine le_antisymm (sup_le hYP inf_le_left) fun p hp => ?_
  have h0 : s3_psi h.norm ⟨p, hp⟩ ∈ s3_img h.norm Y := by rw [hY]; exact Subgroup.mem_top _
  obtain ⟨x, hxY, hx⟩ := s3_mem_img.1 h0
  have hk : p * (x : G)⁻¹ ∈ P ⊓ centralizer (V₀ : Set G) := by
    refine ⟨P.mul_mem hp (P.inv_mem x.2), ?_⟩
    have h1 : s3_psi h.norm (⟨p, hp⟩ * x⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hx, mul_inv_cancel]
    exact (s3_psi_eq_one_iff h.norm _).1 h1
  have e : p = (p * (x : G)⁻¹) * x := by group
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup hk hxY

theorem s3_eq_of_sup_ker_eq {Y : Subgroup G} (hYP : Y ≤ P) (hQY : pCoreOf 2 P ≤ Y)
    (hYK : Y ⊔ (P ⊓ centralizer (V₀ : Set G)) = P) : Y = P := by
  have hfr := h.minParabolic.map_kerIn_subgroupOf_eq_frattini
  rw [h.kerIn_eq] at hfr
  have htop := s3_frattini_step (X := ↥P) (Y.subgroupOf P)
    ((P ⊓ centralizer (V₀ : Set G)).subgroupOf P) ?_ hfr.le ?_
  · exact le_antisymm hYP (Subgroup.subgroupOf_eq_top.1 htop)
  · intro z hz
    have hz' : (z : G) ∈ pCoreOf 2 P := ⟨z, hz, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (hQY hz')
  · rw [← Subgroup.subgroupOf_sup hYP inf_le_left, hYK, Subgroup.subgroupOf_self]

theorem s3_hGen_sup_pCoreOf (hS : S ≤ T₁) (hSn : T₁ ≤ normalizer (S : Set G))
    (hSact : ¬ S ≤ centralizer (V₀ : Set G)) : hGen P S ⊔ pCoreOf 2 P = P := by
  have hHP := h.s3_hGen_le hS
  have htop : s3_img h.norm (hGen P S) = ⊤ :=
    h.s3_img_eq_top hS hSact (s3_le_hGen P S) (h.s3_twoResidual_le_hGen hS hSn hSact)
  refine h.s3_eq_of_sup_ker_eq (sup_le hHP (CFSG.LieType.BorelTits.pCoreOf_le 2 P)) le_sup_right ?_
  refine le_antisymm (sup_le (sup_le hHP (CFSG.LieType.BorelTits.pCoreOf_le 2 P)) inf_le_left) ?_
  calc P = hGen P S ⊔ (P ⊓ centralizer (V₀ : Set G)) :=
        (h.s3_sup_ker_eq_of_img_eq_top hHP htop).symm
    _ ≤ (hGen P S ⊔ pCoreOf 2 P) ⊔ (P ⊓ centralizer (V₀ : Set G)) :=
        sup_le_sup_right le_sup_left _

theorem s3_relIndex_le_two (hS : S ≤ T₁) : (S ⊓ centralizer (V₀ : Set G)).relIndex S ≤ 2 := by
  have hSP : S ≤ P := hS.trans h.le
  let φ : ↥S →* MulAut ↥V₀ := (s3_psi h.norm).comp (Subgroup.inclusion hSP)
  have hker : φ.ker = (centralizer (V₀ : Set G)).subgroupOf S := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact s3_psi_eq_one_iff h.norm _
  have hS2 : IsPGroup 2 S := h.pgroup.to_le hS
  have hpg : IsPGroup 2 φ.range := by
    rintro ⟨σ, x, rfl⟩
    obtain ⟨k, hk⟩ := hS2 x
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← map_pow, hk, map_one]
    rfl
  rw [Subgroup.inf_relIndex_left, Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact s3_card_le_two_of_isPGroup h.s3_card_aut hpg

end S3Frame

theorem S3Frame.package {P T₁ V₀ S : Subgroup G} (h : S3Frame P T₁ V₀) (hS : S ≤ T₁)
    (hSn : T₁ ≤ normalizer (S : Set G)) (hSact : ¬ S ≤ centralizer (V₀ : Set G)) :
    (S ≤ hGen P S ∧ twoResidual P ≤ hGen P S ∧ hGen P S ≤ P ∧ P ≤ normalizer (hGen P S : Set G)) ∧
    (∀ x ∈ P, ∃ h ∈ hGen P S, ∃ o ∈ pCoreOf 2 P, x = h * o) ∧
    pCoreOf 2 (hGen P S) = hGen P S ⊓ pCoreOf 2 P ∧
    hGen P S ⊓ centralizer (pCoreOf 2 (hGen P S) : Set G) ≤ pCoreOf 2 (hGen P S) ∧
    pCoreOf 2 P ≤ centralizer (V₀ : Set G) ∧ V₀ ≤ twoResidual P ∧
    S ⊓ centralizer (V₀ : Set G) ≤ pCoreOf 2 P ∧
    (S ⊓ centralizer (V₀ : Set G)).relIndex S ≤ 2 ∧
    (∀ X : Subgroup G, X ≤ hGen P S → pCoreOf 2 (hGen P S) ≤ X →
      X ⊔ (hGen P S ⊓ centralizer (V₀ : Set G)) = hGen P S → X = hGen P S) ∧
    Nat.card (MulAut ↥V₀) = 6 ∧
    (∀ g : MulAut ↥V₀, ∃ h ∈ hGen P S, ∀ v : ↥V₀, ((g v : ↥V₀) : G) = h * (v : G) * h⁻¹) := by
  have hHP := h.s3_hGen_le hS
  have hHn := h.s3_le_normalizer_hGen hSn
  have hLH := h.s3_twoResidual_le_hGen hS hSn hSact
  have hPeq := h.s3_hGen_sup_pCoreOf hS hSn hSact
  have hQn : P ≤ normalizer (pCoreOf 2 P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hQP : pCoreOf 2 P ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hRe := s3_pCoreOf_eq_inf hHP hHn
  have hHV : ¬ P ≤ centralizer (V₀ : Set G) := fun hle => h.act (h.le.trans hle)
  have hinf := h.minParabolic.inf_centralizer_eq_pCoreOf h.isTwoReduced hHV
  refine ⟨⟨s3_le_hGen P S, hLH, hHP, hHn⟩, ?_, hRe, s3_fstar_of_normal hHP hHn h.fstar,
    MinParabolic.pCoreOf_le_centralizer h.isTwoReduced, h.s3_le_twoResidual,
    (inf_le_inf_right _ hS).trans hinf.le, h.s3_relIndex_le_two hS, ?_, h.s3_card_aut, ?_⟩
  · intro x hx
    have hx' : x ∈ ((hGen P S ⊔ pCoreOf 2 P : Subgroup G) : Set G) := by rw [hPeq]; exact hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hHP.trans hQn)] at hx'
    obtain ⟨y, hy, o, ho, rfl⟩ := hx'
    exact ⟨y, hy, o, ho, rfl⟩
  · intro X hXH hRX hXC
    have hXP : X ≤ P := hXH.trans hHP
    have hY : X ⊔ pCoreOf 2 P = P := by
      refine h.s3_eq_of_sup_ker_eq (sup_le hXP hQP) le_sup_right ?_
      refine le_antisymm (sup_le (sup_le hXP hQP) inf_le_left) ?_
      calc P = hGen P S ⊔ pCoreOf 2 P := hPeq.symm
        _ = (X ⊔ (hGen P S ⊓ centralizer (V₀ : Set G))) ⊔ pCoreOf 2 P := by rw [hXC]
        _ ≤ (X ⊔ pCoreOf 2 P) ⊔ (P ⊓ centralizer (V₀ : Set G)) := by
            refine sup_le (sup_le ?_ ?_) ?_
            · exact le_sup_of_le_left le_sup_left
            · exact le_sup_of_le_right (le_inf (inf_le_left.trans hHP) inf_le_right)
            · exact le_sup_of_le_left le_sup_right
    refine le_antisymm hXH fun x hx => ?_
    have hx' : x ∈ ((X ⊔ pCoreOf 2 P : Subgroup G) : Set G) := by rw [hY]; exact hHP hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hXP.trans hQn)] at hx'
    obtain ⟨a, ha, q, hq, rfl⟩ := hx'
    have hqH : q ∈ hGen P S := by
      have := (hGen P S).mul_mem ((hGen P S).inv_mem (hXH ha)) hx
      simpa using this
    have hqR : q ∈ pCoreOf 2 (hGen P S) := by rw [hRe]; exact ⟨hqH, hq⟩
    exact X.mul_mem ha (hRX hqR)
  · intro g
    have htop := h.s3_img_eq_top hS hSact (s3_le_hGen P S) hLH
    have h0 : g ∈ s3_img h.norm (hGen P S) := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨x, hxH, hx⟩ := s3_mem_img.1 h0
    refine ⟨x, hxH, fun v => ?_⟩
    rw [← hx]
    exact s3_psi_coe h.norm x v

end CFSG.LocalAnalysis.UniquenessCase.UC22.P22k2
