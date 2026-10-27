module

public import CFSG.LocalAnalysis.StandardType.GGL45TorusHDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma isPElt_conj_iff' (p : ℕ) {M : Type*} [Group M] (a x : M) :
    GGL45IsPElt p (a * x * a⁻¹) ↔ GGL45IsPElt p x := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h1 : a * x ^ p ^ k * a⁻¹ = 1 := by
      rw [← conj_pow]
      exact hk
    calc x ^ p ^ k = a⁻¹ * (a * x ^ p ^ k * a⁻¹) * a := by group
      _ = a⁻¹ * 1 * a := by rw [h1]
      _ = 1 := by group
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩

private lemma isPElt_conj_inv_iff (p : ℕ) {M : Type*} [Group M] (a x : M) :
    GGL45IsPElt p (a⁻¹ * x * a) ↔ GGL45IsPElt p x := by
  simpa only [inv_inv] using (isPElt_conj_iff' p (a⁻¹) x)

private lemma isPElt_map_iff (p : ℕ) {K : Type*} [Group K] (u : MulAut K) (x : K) :
    GGL45IsPElt p (u x) ↔ GGL45IsPElt p x := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply u.injective
    rw [map_pow, map_one]
    exact hk
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩

private lemma isElemAbelian_map (p : ℕ) {M : Type*} [Group M] (f : M →* M) {E : Subgroup M}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  obtain ⟨hcomm, hpow⟩ := hE
  haveI : IsMulCommutative E := hcomm
  constructor
  · refine IsMulCommutative.mk ?_
    refine Std.Commutative.mk ?_
    intro x y
    apply Subtype.ext
    obtain ⟨ex, hex, hx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨ey, hey, hy⟩ := Subgroup.mem_map.mp y.2
    have h' : ex * ey = ey * ex :=
      congrArg Subtype.val (mul_comm' (M := E) ⟨ex, hex⟩ ⟨ey, hey⟩)
    calc (x : M) * (y : M) = f ex * f ey := by rw [← hx, ← hy]
      _ = f (ex * ey) := (map_mul f ex ey).symm
      _ = f (ey * ex) := by rw [h']
      _ = f ey * f ex := map_mul f ey ex
      _ = (y : M) * (x : M) := by rw [hy, hx]
  · intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hpow e he, map_one]

private lemma eq_inducedAut_of_largeEvenInduces {K : Type*} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {α : MulAut K} {φ : MulAut R}
    (h : LargeEvenInduces θ (fun k k' => k' = α k) φ) :
    φ = (ggInducedAut θ α : MulAut R) := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l => rw [ggInducedAut_apply]; exact h l (α l) rfl

private lemma inducedAut_conj_mul {K : Type*} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (u ψ : MulAut K) :
    (ggInducedAut θ (u⁻¹ * ψ * u) : MulAut R) =
      (ggInducedAut θ u)⁻¹ * ggInducedAut θ ψ *
        ggInducedAut θ u := by
  rw [map_mul, map_mul, map_inv]

private lemma mem_center_of_inv_mem_center {K : Type*} [Group K] (u : MulAut K) {x : K}
    (h : u⁻¹ x ∈ Subgroup.center K) : x ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff] at h ⊢
  intro g
  obtain ⟨y, rfl⟩ := u.surjective g
  have := congrArg u (h y)
  simpa [map_mul] using this

private lemma not_mem_center_map_inv {K : Type*} [Group K] (u : MulAut K) {x : K}
    (hx : x ∉ Subgroup.center K) : u⁻¹ x ∉ Subgroup.center K :=
  fun h => hx (mem_center_of_inv_mem_center u h)

private lemma MulAut_conj_toMonoidHom_apply {K : Type*} [Group K] (a x : MulAut K) :
    (MulAut.conj a).toMonoidHom x = a * x * a⁻¹ := by
  change (MulAut.conj a) x = a * x * a⁻¹
  rw [MulAut.conj_apply]

private lemma comm_conj_iff {K : Type*} [Group K] (a : MulAut K) (E : Subgroup (MulAut K))
    (α : MulAut K) :
    (∀ e ∈ E, (a * α * a⁻¹) * e = e * (a * α * a⁻¹)) ↔
      (∀ e' ∈ E.map (MulAut.conj a⁻¹).toMonoidHom, α * e' = e' * α) := by
  constructor
  · intro h e' he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
    rw [MulAut_conj_toMonoidHom_apply, inv_inv]
    calc α * (a⁻¹ * e * a)
        = a⁻¹ * ((a * α * a⁻¹) * e) * a := by group
      _ = a⁻¹ * (e * (a * α * a⁻¹)) * a := by rw [h e he]
      _ = (a⁻¹ * e * a) * α := by group
  · intro h e he
    have he' : a⁻¹ * e * a ∈ E.map (MulAut.conj a⁻¹).toMonoidHom := by
      rw [Subgroup.mem_map]
      exact ⟨e, he, by rw [MulAut_conj_toMonoidHom_apply, inv_inv]⟩
    have hh := h (a⁻¹ * e * a) he'
    calc (a * α * a⁻¹) * e
        = a * (α * (a⁻¹ * e * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * e * a) * α) * a⁻¹ := by rw [hh]
      _ = e * (a * α * a⁻¹) := by group

private lemma comm_conj_conj_iff {K : Type*} [Group K] (a : MulAut K) (E : Subgroup (MulAut K))
    (α : MulAut K) :
    (∀ e ∈ E, α * e = e * α) ↔
      (∀ e' ∈ E.map (MulAut.conj a).toMonoidHom, (a * α * a⁻¹) * e' = e' * (a * α * a⁻¹)) := by
  constructor
  · intro h e' he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
    rw [MulAut_conj_toMonoidHom_apply]
    calc (a * α * a⁻¹) * (a * e * a⁻¹) = a * (α * e) * a⁻¹ := by group
      _ = a * (e * α) * a⁻¹ := by rw [h e he]
      _ = (a * e * a⁻¹) * (a * α * a⁻¹) := by group
  · intro h e he
    have he' : a * e * a⁻¹ ∈ E.map (MulAut.conj a).toMonoidHom := by
      rw [Subgroup.mem_map]
      exact ⟨e, he, by rw [MulAut_conj_toMonoidHom_apply]⟩
    have hh := h (a * e * a⁻¹) he'
    calc α * e = a⁻¹ * ((a * α * a⁻¹) * (a * e * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * e * a⁻¹) * (a * α * a⁻¹)) * a := by rw [hh]
      _ = e * α := by group

private lemma InS_map_conj_inv_iff {K : Type*} [Group K] {R : Type} [Group R] (p : ℕ)
    (I : Subgroup (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R) (u : MulAut K)
    (E : Subgroup (MulAut K)) (h : K) :
    GGL45InS p (E.map (MulAut.conj u⁻¹).toMonoidHom) h ↔ GGL45InS p E (u h) := by
  unfold GGL45InS
  constructor
  · rintro ⟨hp, hfix⟩
    refine ⟨(isPElt_map_iff p u h).mpr hp, ?_⟩
    intro e he
    have he' : u⁻¹ * e * u ∈ E.map (MulAut.conj u⁻¹).toMonoidHom := by
      rw [Subgroup.mem_map]
      exact ⟨e, he, by rw [MulAut_conj_toMonoidHom_apply, inv_inv]⟩
    have hh := hfix (u⁻¹ * e * u) he'
    have := congrArg (fun z => u z) hh
    simpa [MulAut.mul_apply] using this
  · rintro ⟨hp, hfix⟩
    refine ⟨(isPElt_map_iff p u h).mp hp, ?_⟩
    intro e' he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
    rw [MulAut_conj_toMonoidHom_apply, inv_inv, MulAut.mul_apply, MulAut.mul_apply]
    rw [hfix e he]
    simp

private lemma inducesIn_conj_mul_iff {K : Type*} [Group K] {R : Type} [Group R]
    (I : Subgroup (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R) (u : MulAut K)
    (hu : GGL45InducesIn θ (I : Set (MulAut R)) u) (α : MulAut K) :
    GGL45InducesIn θ (I : Set (MulAut R)) (u * α * u⁻¹) ↔
      GGL45InducesIn θ (I : Set (MulAut R)) α := by
  rw [ggL45_inducesIn_iff, ggL45_inducesIn_iff]
  have hūI : ggInducedAut θ u ∈ I := (ggL45_inducesIn_iff θ (I : Set (MulAut R)) u).1 hu
  have hmap : ggInducedAut θ (u * α * u⁻¹) =
      ggInducedAut θ u * ggInducedAut θ α * (ggInducedAut θ u)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [hmap]
  constructor
  · intro h
    have h2 : (ggInducedAut θ u)⁻¹ *
        (ggInducedAut θ u * ggInducedAut θ α * (ggInducedAut θ u)⁻¹) *
        ggInducedAut θ u ∈ I :=
      I.mul_mem (I.mul_mem (I.inv_mem hūI) h) hūI
    have heq : (ggInducedAut θ u)⁻¹ *
        (ggInducedAut θ u * ggInducedAut θ α * (ggInducedAut θ u)⁻¹) *
        ggInducedAut θ u = ggInducedAut θ α := by group
    rwa [heq] at h2
  · intro h
    exact I.mul_mem (I.mul_mem hūI h) (I.inv_mem hūI)

private lemma inducesIn_conj_inv_iff {K : Type*} [Group K] {R : Type} [Group R]
    (I : Subgroup (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R) (u : MulAut K)
    (hu : GGL45InducesIn θ (I : Set (MulAut R)) u) (α : MulAut K) :
    GGL45InducesIn θ (I : Set (MulAut R)) (u⁻¹ * α * u) ↔
      GGL45InducesIn θ (I : Set (MulAut R)) α := by
  have h := inducesIn_conj_mul_iff I θ u hu (u⁻¹ * α * u)
  have heq : u * (u⁻¹ * α * u) * u⁻¹ = α := by group
  rw [heq] at h
  exact h.symm

private lemma InCIp_map_conj_inv_iff {K : Type*} [Group K] {R : Type} [Group R] (p : ℕ)
    (I : Subgroup (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R) (u : MulAut K)
    (hūI : ggInducedAut θ u ∈ I)
    (E : Subgroup (MulAut K)) (x : MulAut R) :
    GGL45InCIp p (I : Set (MulAut R)) θ (E.map (MulAut.conj u⁻¹).toMonoidHom) x ↔
      GGL45InCIp p (I : Set (MulAut R)) θ E
        (ggInducedAut θ u * x * (ggInducedAut θ u)⁻¹) := by
  unfold GGL45InCIp
  constructor
  · rintro ⟨hxI, hxcomm, hxp⟩
    refine ⟨I.mul_mem (I.mul_mem hūI hxI) (I.inv_mem hūI), ?_,
      (isPElt_conj_iff' p (ggInducedAut θ u) x).mpr hxp⟩
    intro e he
    have he' : u⁻¹ * e * u ∈ E.map (MulAut.conj u⁻¹).toMonoidHom := by
      rw [Subgroup.mem_map]
      exact ⟨e, he, by rw [MulAut_conj_toMonoidHom_apply, inv_inv]⟩
    have hh := hxcomm (u⁻¹ * e * u) he'
    have hga : ggInducedAut θ (u⁻¹ * e * u) =
        (ggInducedAut θ u)⁻¹ * ggInducedAut θ e * ggInducedAut θ u := by
      rw [map_mul, map_mul, map_inv]
    rw [hga] at hh
    calc (ggInducedAut θ u * x * (ggInducedAut θ u)⁻¹) * ggInducedAut θ e
        = ggInducedAut θ u *
            (x * ((ggInducedAut θ u)⁻¹ * ggInducedAut θ e * ggInducedAut θ u)) *
            (ggInducedAut θ u)⁻¹ := by group
      _ = ggInducedAut θ u *
            (((ggInducedAut θ u)⁻¹ * ggInducedAut θ e * ggInducedAut θ u) * x) *
            (ggInducedAut θ u)⁻¹ := by rw [hh]
      _ = ggInducedAut θ e * (ggInducedAut θ u * x * (ggInducedAut θ u)⁻¹) := by group
  · rintro ⟨hI, hcomm, hp⟩
    refine ⟨?_, ?_, (isPElt_conj_iff' p (ggInducedAut θ u) x).mp hp⟩
    · have h2 : (ggInducedAut θ u)⁻¹ *
          (ggInducedAut θ u * x * (ggInducedAut θ u)⁻¹) * (ggInducedAut θ u) ∈ I :=
        I.mul_mem (I.mul_mem (I.inv_mem hūI) hI) hūI
      have heq : (ggInducedAut θ u)⁻¹ *
          (ggInducedAut θ u * x * (ggInducedAut θ u)⁻¹) *
          (ggInducedAut θ u) = x := by group
      rwa [heq] at h2
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
      rw [MulAut_conj_toMonoidHom_apply, inv_inv]
      have hh := hcomm e he
      have hga : ggInducedAut θ (u⁻¹ * e * u) =
          (ggInducedAut θ u)⁻¹ * ggInducedAut θ e * ggInducedAut θ u := by
        rw [map_mul, map_mul, map_inv]
      rw [hga]
      calc x * ((ggInducedAut θ u)⁻¹ * ggInducedAut θ e * ggInducedAut θ u)
          = (ggInducedAut θ u)⁻¹ *
              ((ggInducedAut θ u * x * (ggInducedAut θ u)⁻¹) * ggInducedAut θ e) *
              ggInducedAut θ u := by group
        _ = (ggInducedAut θ u)⁻¹ *
              (ggInducedAut θ e * (ggInducedAut θ u * x * (ggInducedAut θ u)⁻¹)) *
              ggInducedAut θ u := by rw [hh]
        _ = ((ggInducedAut θ u)⁻¹ * ggInducedAut θ e * ggInducedAut θ u) * x := by group

section Package

variable (p : ℕ) {K : Type*} [Group K] {R : Type} [Group R] (I : Subgroup (MulAut R))
  (θ : K ⧸ Subgroup.center K ≃* R) (u : MulAut K)

theorem ggL45TorusH_conj (hu : GGL45InducesIn θ (I : Set (MulAut R)) u) (ψ : MulAut K)
    (E : Subgroup (MulAut K)) (h : GGL45TorusH p (I : Set (MulAut R)) θ ψ E) :
    GGL45TorusH p (I : Set (MulAut R)) θ (u⁻¹ * ψ * u) (E.map (MulAut.conj u⁻¹).toMonoidHom) := by
  obtain ⟨s, hs, c, k, hk, hc, H1, H2, H3, H4mod⟩ := h
  have hūI : ggInducedAut θ u ∈ I := (ggL45_inducesIn_iff θ (I : Set (MulAut R)) u).1 hu
  refine ⟨s, hs, c, k, hk, hc, ?_, ?_, ?_, ?_⟩
  · unfold GGL45HOne at H1 ⊢
    obtain ⟨H1a, H1b⟩ := H1
    constructor
    · intro x y hx hy
      have hx' := (InCIp_map_conj_inv_iff p I θ u hūI E x).mp hx
      have hy' := (InCIp_map_conj_inv_iff p I θ u hūI E y).mp hy
      have hh := H1a (ggInducedAut θ u * x * (ggInducedAut θ u)⁻¹)
        (ggInducedAut θ u * y * (ggInducedAut θ u)⁻¹) hx' hy'
      calc x * y = (ggInducedAut θ u)⁻¹ *
            ((ggInducedAut θ u * x * (ggInducedAut θ u)⁻¹) *
              (ggInducedAut θ u * y * (ggInducedAut θ u)⁻¹)) * ggInducedAut θ u := by group
        _ = (ggInducedAut θ u)⁻¹ *
            ((ggInducedAut θ u * y * (ggInducedAut θ u)⁻¹) *
              (ggInducedAut θ u * x * (ggInducedAut θ u)⁻¹)) * ggInducedAut θ u := by rw [hh]
        _ = y * x := by group
    · intro x hx
      have hx' := (InCIp_map_conj_inv_iff p I θ u hūI E x).mp hx
      obtain ⟨hpow, hact⟩ := H1b (ggInducedAut θ u * x * (ggInducedAut θ u)⁻¹) hx'
      constructor
      · have hcz := conj_pow (a := ggInducedAut θ u) (b := x) (i := p ^ s)
        rw [hcz] at hpow
        calc x ^ p ^ s = (ggInducedAut θ u)⁻¹ *
              (ggInducedAut θ u * x ^ p ^ s * (ggInducedAut θ u)⁻¹) * ggInducedAut θ u := by group
          _ = (ggInducedAut θ u)⁻¹ * 1 * ggInducedAut θ u := by rw [hpow]
          _ = 1 := by group
      · rw [inducedAut_conj_mul θ u ψ]
        calc ((ggInducedAut θ u)⁻¹ * ggInducedAut θ ψ * ggInducedAut θ u) * x *
              ((ggInducedAut θ u)⁻¹ * ggInducedAut θ ψ * ggInducedAut θ u)⁻¹
            = (ggInducedAut θ u)⁻¹ *
                (ggInducedAut θ ψ * (ggInducedAut θ u * x * (ggInducedAut θ u)⁻¹) *
                  (ggInducedAut θ ψ)⁻¹) * ggInducedAut θ u := by group
          _ = (ggInducedAut θ u)⁻¹ *
                (ggInducedAut θ u * x * (ggInducedAut θ u)⁻¹) ^ c * ggInducedAut θ u := by rw [hact]
          _ = x ^ c := by
                have hcz := conj_zpow (a := (ggInducedAut θ u)⁻¹)
                  (b := ggInducedAut θ u * x * (ggInducedAut θ u)⁻¹) (i := c)
                simp only [inv_inv] at hcz
                rw [← hcz]
                congr 1
                group
  · unfold GGL45HTwo at H2 ⊢
    obtain ⟨H2a, H2b, H2c⟩ := H2
    constructor
    · intro h t hh ht
      have hh' := (InS_map_conj_inv_iff p I θ u E h).mp hh
      have ht' := (InS_map_conj_inv_iff p I θ u E t).mp ht
      have hh2 := H2a (u h) (u t) hh' ht'
      apply u.injective
      rw [map_mul, map_mul]
      exact hh2
    constructor
    · intro h hh
      have hh' := (InS_map_conj_inv_iff p I θ u E h).mp hh
      obtain ⟨hpow, hact⟩ := H2b (u h) hh'
      constructor
      · apply u.injective
        rw [map_pow, map_one]
        exact hpow
      · rw [MulAut.mul_apply, MulAut.mul_apply, hact, ← map_zpow]
        simp
    · intro α hα hcommα h hh
      have hα' := (inducesIn_conj_mul_iff I θ u hu α).mpr hα
      have hcommα' := (comm_conj_iff u E α).mpr hcommα
      have hh' := (InS_map_conj_inv_iff p I θ u E h).mp hh
      have hh2 := H2c (u * α * u⁻¹) hα' hcommα' (u h) hh'
      apply u.injective
      simpa [MulAut.mul_apply] using hh2
  · unfold GGL45HThree at H3 ⊢
    obtain ⟨⟨h₀, hh₀, hnc₀⟩, b₁, b₂, ⟨h₁, hh₁, hb₁⟩, ⟨h₂, hh₂, hb₂⟩, hb₁nc, hbind⟩ := H3
    refine ⟨⟨u⁻¹ h₀, ?_, ?_⟩, u⁻¹ b₁, u⁻¹ b₂, ?_, ?_, ?_, ?_⟩
    · exact (InS_map_conj_inv_iff p I θ u E (u⁻¹ h₀)).mpr (by simpa using hh₀)
    · rw [← map_pow]
      exact not_mem_center_map_inv u hnc₀
    · refine ⟨u⁻¹ h₁, ?_, ?_⟩
      · exact (InS_map_conj_inv_iff p I θ u E (u⁻¹ h₁)).mpr (by simpa using hh₁)
      · rw [hb₁, map_pow]
    · refine ⟨u⁻¹ h₂, ?_, ?_⟩
      · exact (InS_map_conj_inv_iff p I θ u E (u⁻¹ h₂)).mpr (by simpa using hh₂)
      · rw [hb₂, map_pow]
    · exact not_mem_center_map_inv u hb₁nc
    · intro i j hij
      apply hbind i j
      apply (u⁻¹).injective
      simpa only [map_mul, map_pow, map_one] using hij
  · unfold GGL45HFourMod at H4mod ⊢
    intro α hα hcommα hαnotI hαpI
    have hβp : GGL45IsPElt p (ggInducedAut θ u * α * (ggInducedAut θ u)⁻¹) :=
      (isPElt_conj_iff' p (ggInducedAut θ u) α).mpr hα
    have hβcomm : ∀ e ∈ E, (ggInducedAut θ u * α * (ggInducedAut θ u)⁻¹) * ggInducedAut θ e
        = ggInducedAut θ e * (ggInducedAut θ u * α * (ggInducedAut θ u)⁻¹) := by
      intro e he
      have he' : u⁻¹ * e * u ∈ E.map (MulAut.conj u⁻¹).toMonoidHom := by
        rw [Subgroup.mem_map]
        exact ⟨e, he, by rw [MulAut_conj_toMonoidHom_apply, inv_inv]⟩
      have hh := hcommα (u⁻¹ * e * u) he'
      have hga : ggInducedAut θ (u⁻¹ * e * u) =
          (ggInducedAut θ u)⁻¹ * ggInducedAut θ e * ggInducedAut θ u := by
        rw [map_mul, map_mul, map_inv]
      rw [hga] at hh
      calc (ggInducedAut θ u * α * (ggInducedAut θ u)⁻¹) * ggInducedAut θ e
          = ggInducedAut θ u *
              (α * ((ggInducedAut θ u)⁻¹ * ggInducedAut θ e * ggInducedAut θ u)) *
              (ggInducedAut θ u)⁻¹ := by group
        _ = ggInducedAut θ u *
              (((ggInducedAut θ u)⁻¹ * ggInducedAut θ e * ggInducedAut θ u) * α) *
              (ggInducedAut θ u)⁻¹ := by rw [hh]
        _ = ggInducedAut θ e * (ggInducedAut θ u * α * (ggInducedAut θ u)⁻¹) := by group
    have hβnotI : ggInducedAut θ u * α * (ggInducedAut θ u)⁻¹ ∉ I := by
      intro hh
      apply hαnotI
      have h2 : (ggInducedAut θ u)⁻¹ *
          (ggInducedAut θ u * α * (ggInducedAut θ u)⁻¹) * ggInducedAut θ u ∈ I :=
        I.mul_mem (I.mul_mem (I.inv_mem hūI) hh) hūI
      have heq : (ggInducedAut θ u)⁻¹ *
          (ggInducedAut θ u * α * (ggInducedAut θ u)⁻¹) *
          ggInducedAut θ u = α := by group
      rwa [heq] at h2
    have hβpI : (ggInducedAut θ u * α * (ggInducedAut θ u)⁻¹) ^ p ∈ I := by
      have hcz := conj_pow (a := ggInducedAut θ u) (b := α) (i := p)
      rw [hcz]
      exact I.mul_mem (I.mul_mem hūI hαpI) (I.inv_mem hūI)
    obtain ⟨j, hj, hmem⟩ :=
      H4mod (ggInducedAut θ u * α * (ggInducedAut θ u)⁻¹) hβp hβcomm hβnotI hβpI
    refine ⟨j, hj, ?_⟩
    have hconj : α * ((ggInducedAut θ (u⁻¹ * ψ * u)) ^ j)⁻¹ =
        (ggInducedAut θ u)⁻¹ *
          ((ggInducedAut θ u * α * (ggInducedAut θ u)⁻¹) *
            ((ggInducedAut θ ψ) ^ j)⁻¹) * ggInducedAut θ u := by
      rw [inducedAut_conj_mul θ u ψ]
      rw [show ((ggInducedAut θ u)⁻¹ * ggInducedAut θ ψ * ggInducedAut θ u) ^ j
            = (ggInducedAut θ u)⁻¹ * (ggInducedAut θ ψ) ^ j * ggInducedAut θ u from by
            simpa only [inv_inv] using
              (conj_pow (a := (ggInducedAut θ u)⁻¹) (b := ggInducedAut θ ψ) (i := j))]
      group
    rw [hconj]
    exact I.mul_mem (I.mul_mem (I.inv_mem hūI) hmem) hūI

end Package

section Hyp

variable (p : ℕ) (lab : LargeEvenLabel) {K : Type} [Group K] {R : Type} [Group R]
  (I : Subgroup (MulAut R)) (F : Set (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R) (u : MulAut K)

theorem ggL45TorusKGHyp_conj (hu : GGL45InducesIn θ (I : Set (MulAut R)) u) (ψ : MulAut K)
    (E : Subgroup (MulAut K)) (h : GGL45TorusKGHyp p lab (I : Set (MulAut R)) F θ ψ E) :
    GGL45TorusKGHyp p lab (I : Set (MulAut R)) F θ (u⁻¹ * ψ * u)
      (E.map (MulAut.conj u⁻¹).toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have hūI : ggInducedAut θ u ∈ I := (ggL45_inducesIn_iff θ (I : Set (MulAut R)) u).1 hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcz := conj_pow (a := u⁻¹) (b := ψ) (i := p)
    simp only [inv_inv] at hcz
    rw [hcz, h1]
    group
  · obtain ⟨f, hf, w, hw, hord, hind⟩ := h2
    have hwind : w * f * w⁻¹ = ggInducedAut θ ψ := eq_inducedAut_of_largeEvenInduces θ hind
    refine ⟨f, hf, (ggInducedAut θ u)⁻¹ * w, I.mul_mem (I.inv_mem hūI) hw, hord, ?_⟩
    have h' : (ggInducedAut θ u)⁻¹ * w * f * ((ggInducedAut θ u)⁻¹ * w)⁻¹ =
        ggInducedAut θ (u⁻¹ * ψ * u) := by
      rw [inducedAut_conj_mul θ u ψ]
      rw [← hwind]
      group
    rw [h']
    exact ggL45_largeEvenInduces_inducedAut θ (u⁻¹ * ψ * u)
  · exact isElemAbelian_map p (MulAut.conj u⁻¹).toMonoidHom h3
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj u⁻¹).toMonoidHom) (MulEquiv.injective _)]
    exact h4
  · intro ht hr hp3
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj u⁻¹).toMonoidHom) (MulEquiv.injective _)]
    exact h5 ht hr hp3
  · intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.mp he
    rw [MulAut_conj_toMonoidHom_apply, inv_inv]
    exact (inducesIn_conj_inv_iff I θ u hu e₀).mpr (h6 e₀ he₀)
  · intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.mp he
    rw [MulAut_conj_toMonoidHom_apply, inv_inv]
    calc (u⁻¹ * e₀ * u) * (u⁻¹ * ψ * u) = u⁻¹ * (e₀ * ψ) * u := by group
      _ = u⁻¹ * (ψ * e₀) * u := by rw [h7 e₀ he₀]
      _ = (u⁻¹ * ψ * u) * (u⁻¹ * e₀ * u) := by group
  · intro k hkp hfix hψ
    have hkp' : (u k) ^ p = 1 := by rw [← map_pow, hkp, map_one]
    have hfix' : ∀ e ∈ E, e (u k) = u k := by
      intro e he
      have he' : u⁻¹ * e * u ∈ E.map (MulAut.conj u⁻¹).toMonoidHom := by
        rw [Subgroup.mem_map]
        exact ⟨e, he, by rw [MulAut_conj_toMonoidHom_apply, inv_inv]⟩
      have hh := hfix (u⁻¹ * e * u) he'
      have := congrArg (fun z => u z) hh
      simpa [MulAut.mul_apply] using this
    have hψ' : ψ (u k) = u k := by
      have := congrArg (fun z => u z) hψ
      simpa [MulAut.mul_apply] using this
    have hconj : MulAut.conj (u k) ∈ E := h8 (u k) hkp' hfix' hψ'
    have hconj_eq : MulAut.conj k = u⁻¹ * MulAut.conj (u k) * u := by
      ext x
      simp [MulAut.mul_apply, MulAut.conj_apply]
    rw [hconj_eq]
    rw [Subgroup.mem_map]
    exact ⟨MulAut.conj (u k), hconj, by rw [MulAut_conj_toMonoidHom_apply, inv_inv]⟩
  · intro R₀ Q hR₀ hR₀ψ hQ hQne hQψ hnorm
    have hR₀' : IsElemAbelian p (R₀.map u.toMonoidHom) := isElemAbelian_map p u.toMonoidHom hR₀
    have hR₀'ψ : ∀ r ∈ R₀.map u.toMonoidHom, ψ r = r := by
      intro r hr
      obtain ⟨r₀, hr₀, rfl⟩ := Subgroup.mem_map.mp hr
      change ψ (u r₀) = u r₀
      have hga : ψ (u r₀) = u ((u⁻¹ * ψ * u) r₀) := by simp [MulAut.mul_apply]
      rw [hga, hR₀ψ r₀ hr₀]
    have hQ' : IsPGroup 2 (Q.map u.toMonoidHom) := IsPGroup.map hQ u.toMonoidHom
    have hQ'ne : Q.map u.toMonoidHom ≠ ⊥ := fun h =>
      hQne ((Subgroup.map_eq_bot_iff_of_injective (f := u.toMonoidHom) Q (MulEquiv.injective u)).mp h)
    have hQ'ψ : ∀ g ∈ Q.map u.toMonoidHom, ψ g ∈ Q.map u.toMonoidHom := by
      intro g hg
      obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hg
      change ψ (u g₀) ∈ Q.map u.toMonoidHom
      have hga : ψ (u g₀) = u ((u⁻¹ * ψ * u) g₀) := by simp [MulAut.mul_apply]
      rw [hga]
      exact Subgroup.mem_map_of_mem u.toMonoidHom (hQψ g₀ hg₀)
    have hnorm' : R₀.map u.toMonoidHom ≤ Subgroup.normalizer (Q.map u.toMonoidHom : Set K) :=
      le_trans (Subgroup.map_mono hnorm) (Subgroup.le_normalizer_map (H := Q) u.toMonoidHom)
    obtain ⟨hcard, hcard2⟩ :=
      h9 (R₀.map u.toMonoidHom) (Q.map u.toMonoidHom) hR₀' hR₀'ψ hQ' hQ'ne hQ'ψ hnorm'
    refine ⟨?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj u⁻¹).toMonoidHom)
        (MulEquiv.injective _)]
      rw [Subgroup.card_map_of_injective (f := u.toMonoidHom) (MulEquiv.injective u)] at hcard
      exact hcard
    · intro hcop
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj u⁻¹).toMonoidHom)
        (MulEquiv.injective _)]
      rw [Subgroup.card_map_of_injective (f := u.toMonoidHom) (MulEquiv.injective u)] at hcard2
      exact hcard2 hcop
  · obtain ⟨P, hPE, hcardP, hP⟩ := h10
    refine ⟨P.map (MulAut.conj u⁻¹).toMonoidHom, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map_of_mem _ (hPE he)
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj u⁻¹).toMonoidHom)
          (MulEquiv.injective _),
        Subgroup.card_map_of_injective (f := (MulAut.conj u⁻¹).toMonoidHom)
          (MulEquiv.injective _)]
      exact hcardP
    · intro e he
      obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.mp he
      obtain ⟨γ, hγp, hγcomm, hγgrp, heq⟩ := hP e₀ he₀
      refine ⟨u⁻¹ * γ * u, (isPElt_conj_inv_iff p u γ).mpr hγp, ?_, ?_, ?_⟩
      · exact (comm_conj_conj_iff u⁻¹ E γ).mp hγcomm
      · have hset : (MulAut.conj u⁻¹).toMonoidHom ''
            (insert γ (insert ψ (E : Set (MulAut K)))) =
            insert (u⁻¹ * γ * u)
              (insert (u⁻¹ * ψ * u) (E.map (MulAut.conj u⁻¹).toMonoidHom : Set (MulAut K))) := by
          rw [Set.image_insert_eq, Set.image_insert_eq, ← Subgroup.coe_map]
          simp only [MulAut_conj_toMonoidHom_apply, inv_inv]
        have hclosure : Subgroup.closure
              (insert (u⁻¹ * γ * u)
                (insert (u⁻¹ * ψ * u)
                  (E.map (MulAut.conj u⁻¹).toMonoidHom : Set (MulAut K)))) =
            (Subgroup.closure (insert γ (insert ψ (E : Set (MulAut K))))).map
              (MulAut.conj u⁻¹).toMonoidHom := by
          rw [MonoidHom.map_closure, hset]
        rw [hclosure]
        exact IsPGroup.map hγgrp (MulAut.conj u⁻¹).toMonoidHom
      · rw [MulAut_conj_toMonoidHom_apply, inv_inv]
        rw [heq]
        group

end Hyp

end CFSG.StandardType
