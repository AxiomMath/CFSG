module

public import CFSG.RankThree.PartOne.KF.D8Ctx
public import CFSG.RankThree.PartOne.S12.KFTransfer

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU

variable {G : Type} [Group G] {p : ℕ} {K : Type} [Field K] {c : G} {L E F : Subgroup G}

@[expose] noncomputable def weylE (S : D8Ctx p K L F) (R : Sec12Three.Restr c L E F) (hp : p.Prime)
    (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) : ↥(torusImage E L) ≃* DihedralGroup 4 :=
  (Classical.choose R.exists_resE).trans (S.weylEquiv hp hp2 hζ)

theorem actF_weylEquiv (S : D8Ctx p K L F) (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (ψ : ↥(torusImage F L)) :
    S.actF (S.weylEquiv hp hp2 hζ ψ) = (ψ : MulAut F) := by
  have h := (MonoidHom.ofInjective (S.actF_injective hp hp2 hζ)).apply_symm_apply
    ⟨(ψ : MulAut F), S.torusImage_eq_range ▸ ψ.2⟩
  exact congrArg Subtype.val h

theorem normalizerMonoidHom_restrict_eq (R : Sec12Three.Restr c L E F) {x y : G}
    (hxE : x ∈ Subgroup.normalizer (E : Set G)) (hxF : x ∈ Subgroup.normalizer (F : Set G))
    (hyE : y ∈ Subgroup.normalizer (E : Set G)) (hyF : y ∈ Subgroup.normalizer (F : Set G))
    (h : E.normalizerMonoidHom ⟨x, hxE⟩ = E.normalizerMonoidHom ⟨y, hyE⟩) :
    F.normalizerMonoidHom ⟨x, hxF⟩ = F.normalizerMonoidHom ⟨y, hyF⟩ := by
  ext f
  have h1 := Sec12Three.coe_normalizerMonoidHom_restrict R.F_le_E hxE hxF f
  have h2 := Sec12Three.coe_normalizerMonoidHom_restrict R.F_le_E hyE hyF f
  have h3 := congrArg (fun φ : MulAut E => ((φ ⟨f, R.F_le_E f.2⟩ : E) : G)) h
  rw [h1, h2]
  exact h3

theorem actF_weylE (S : D8Ctx p K L F) (R : Sec12Three.Restr c L E F) (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) {x : G} (hxL : x ∈ L)
    (hxE : x ∈ Subgroup.normalizer (E : Set G)) (hxF : x ∈ Subgroup.normalizer (F : Set G)) :
    S.actF (weylE S R hp hp2 hζ ⟨conjAut E x hxE, Sec12Three.mem_torusImage_iff.mpr
      ⟨x, hxL, hxE, rfl⟩⟩) = F.normalizerMonoidHom ⟨x, hxF⟩ := by
  classical
  set γ : ↥(torusImage E L) := ⟨conjAut E x hxE, Sec12Three.mem_torusImage_iff.mpr
    ⟨x, hxL, hxE, rfl⟩⟩ with hγ
  obtain ⟨x', -, hx'E, hx'F, h1, h2⟩ := Classical.choose_spec R.exists_resE γ
  have hxx' : F.normalizerMonoidHom ⟨x, hxF⟩ = F.normalizerMonoidHom ⟨x', hx'F⟩ :=
    normalizerMonoidHom_restrict_eq R hxE hxF hx'E hx'F h1
  unfold weylE
  rw [MulEquiv.trans_apply, actF_weylEquiv, h2, hxx']

theorem exists_conjAut_of_mem_torusImage {γ : MulAut E} (h : γ ∈ torusImage E L) :
    ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G)), γ = conjAut E x hxE := by
  obtain ⟨x, hxL, hxE, hx⟩ := Sec12Three.mem_torusImage_iff.mp h
  exact ⟨x, hxL, hxE, hx.symm⟩

theorem isAutReflection_weylE_iff (S : D8Ctx p K L F) (R : Sec12Three.Restr c L E F) (hp : p.Prime)
    (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (γ : ↥(torusImage E L)) :
    IsAutReflection p E (γ : MulAut E) ↔ ∃ i : ZMod 4, weylE S R hp hp2 hζ γ = DihedralGroup.sr i := by
  classical
  obtain ⟨x, hxL, hxE, hxF, h1, h2⟩ := Classical.choose_spec R.exists_resE γ
  set e := Classical.choose R.exists_resE with he
  have hmoved : autMovedInG E (γ : MulAut E) = autMovedInG F ((e γ : ↥(torusImage F L)) : MulAut F) := by
    rw [h1, h2]
    exact R.autMovedInG_eq (R.comm x hxL).symm hxE hxF
  have hcard : Nat.card (autMoved E (γ : MulAut E)) =
      Nat.card (autMoved F ((e γ : ↥(torusImage F L)) : MulAut F)) := by
    rw [← Sec12Three.natCard_autMovedInG, ← Sec12Three.natCard_autMovedInG, hmoved]
  have hord : orderOf (γ : MulAut E) = orderOf ((e γ : ↥(torusImage F L)) : MulAut F) := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  have hE : IsAutReflection p E (γ : MulAut E) ↔
      IsAutReflection p F ((e γ : ↥(torusImage F L)) : MulAut F) := by
    unfold IsAutReflection
    rw [hord, hcard]
  rw [hE]
  have hW : S.actF (weylE S R hp hp2 hζ γ) = ((e γ : ↥(torusImage F L)) : MulAut F) := by
    unfold weylE
    rw [MulEquiv.trans_apply, actF_weylEquiv]
  rw [← hW]
  constructor
  · rintro ⟨hord2, hcard2⟩
    set w := weylE S R hp hp2 hζ γ with hw
    have hord_w : orderOf w = 2 := by
      rw [← orderOf_injective S.actF (S.actF_injective hp hp2 hζ) w]
      exact hord2
    have hw2 : w * w = 1 := by
      rw [← sq]
      have := pow_orderOf_eq_one w
      rwa [hord_w] at this
    have hw1 : w ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hord_w
      omega
    have hc : Nat.card (movedV (d8Act (p := p) (K := K) w)) = p := by
      have := hcard2
      rw [D8Ctx.autMoved_actF, Subgroup.card_map_of_injective S.tor.injective] at this
      exact this
    exact exists_sr_of_card_moved hp hp2 hζ hw2 hw1 hc
  · rintro ⟨i, hi⟩
    rw [hi]
    exact S.isAutReflection_sr hp hp2 hζ i

theorem weylE_fix (S : D8Ctx p K L F) (R : Sec12Three.Restr c L E F) (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (γ : ↥(torusImage E L)) (d : D8Mod p K)
    (hfix : ((((γ : MulAut E) ⟨((S.tor d : F) : G), R.F_le_E (S.tor d).2⟩ : E)) : G) =
      ((S.tor d : F) : G)) :
    d8Act (weylE S R hp hp2 hζ γ) d = d := by
  obtain ⟨x, hxL, hxE, hx⟩ := exists_conjAut_of_mem_torusImage γ.2
  have hxF : x ∈ Subgroup.normalizer (F : Set G) := R.inf_normalizer_le ⟨hxL, hxE⟩
  have hγ : γ = ⟨conjAut E x hxE, Sec12Three.mem_torusImage_iff.mpr ⟨x, hxL, hxE, rfl⟩⟩ :=
    Subtype.ext hx
  have hA := actF_weylE S R hp hp2 hζ hxL hxE hxF
  rw [← hγ] at hA
  have h1 : S.actF (weylE S R hp hp2 hζ γ) (S.tor d) = S.tor d := by
    rw [hA]
    apply Subtype.ext
    have hxconj : ((F.normalizerMonoidHom ⟨x, hxF⟩ (S.tor d) : F) : G) =
        x * ((S.tor d : F) : G) * x⁻¹ := rfl
    have hEconj : ((((γ : MulAut E) ⟨((S.tor d : F) : G), R.F_le_E (S.tor d).2⟩ : E)) : G) =
        x * ((S.tor d : F) : G) * x⁻¹ := by
      rw [hx]
      rfl
    rw [hxconj, ← hEconj]
    exact hfix
  rw [S.actF_apply] at h1
  exact S.tor.injective h1

theorem exists_dihedral_conj_of_parity :
    ∀ i₀ i : ZMod 4, i₀.val % 2 = i.val % 2 →
      ∃ w : DihedralGroup 4, w * DihedralGroup.sr i₀ * w⁻¹ = DihedralGroup.sr i := by
  decide +kernel

theorem exists_dihedral_conj_pair :
    ∀ i₀ i₁ i j : ZMod 4, i₀.val % 2 = i.val % 2 → i₁.val % 2 = j.val % 2 →
      i.val % 2 ≠ j.val % 2 →
      ∃ w : DihedralGroup 4, w * DihedralGroup.sr i₀ * w⁻¹ = DihedralGroup.sr i ∧
        w * DihedralGroup.sr i₁ * w⁻¹ = DihedralGroup.sr j := by
  decide +kernel

theorem dihedral_sr_mul_sr_sq_of_parity :
    ∀ i j : ZMod 4, i.val % 2 = j.val % 2 → (DihedralGroup.sr i * DihedralGroup.sr j) ^ 2 = 1 := by
  decide +kernel

theorem parity_ne_of_orderOf_eq_four {i j : ZMod 4}
    (h : orderOf (DihedralGroup.sr i * DihedralGroup.sr j) = 4) : i.val % 2 ≠ j.val % 2 := by
  intro hpar
  have h2 := dihedral_sr_mul_sr_sq_of_parity i j hpar
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  rw [h] at hdvd
  omega

section Conj

variable (S : D8Ctx p K L F) (R : Sec12Three.Restr c L E F) (hp : p.Prime) (hp2 : p ≠ 2)
  (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)

include S R hp hp2 hζ in
theorem exists_conj_of_parity {t₀ t : MulAut E} {ht₀ : t₀ ∈ torusImage E L}
    {ht : t ∈ torusImage E L} {i₀ i : ZMod 4}
    (h₀ : weylE S R hp hp2 hζ ⟨t₀, ht₀⟩ = DihedralGroup.sr i₀)
    (h : weylE S R hp hp2 hζ ⟨t, ht⟩ = DihedralGroup.sr i) (hpar : i₀.val % 2 = i.val % 2) :
    ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G)),
      t = conjAut E x hxE * t₀ * (conjAut E x hxE)⁻¹ := by
  obtain ⟨w, hw⟩ := exists_dihedral_conj_of_parity i₀ i hpar
  set u : ↥(torusImage E L) := (weylE S R hp hp2 hζ).symm w with hu
  obtain ⟨x, hxL, hxE, hx⟩ := exists_conjAut_of_mem_torusImage u.2
  refine ⟨x, hxL, hxE, ?_⟩
  have h1 : u * ⟨t₀, ht₀⟩ * u⁻¹ = ⟨t, ht⟩ := by
    apply (weylE S R hp hp2 hζ).injective
    rw [map_mul, map_mul, map_inv, hu, MulEquiv.apply_symm_apply, h₀, h, hw]
  have h2 := congrArg (fun y : ↥(torusImage E L) => (y : MulAut E)) h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  rw [← h2, ← hx]

include S R hp hp2 hζ in
theorem exists_conj_pair {t₀ t₁ s s' : MulAut E} {ht₀ : t₀ ∈ torusImage E L}
    {ht₁ : t₁ ∈ torusImage E L} {hs₀ : s ∈ torusImage E L} {hs₁ : s' ∈ torusImage E L}
    {i₀ i₁ i j : ZMod 4}
    (h₀ : weylE S R hp hp2 hζ ⟨t₀, ht₀⟩ = DihedralGroup.sr i₀)
    (h₁ : weylE S R hp hp2 hζ ⟨t₁, ht₁⟩ = DihedralGroup.sr i₁)
    (hs : weylE S R hp hp2 hζ ⟨s, hs₀⟩ = DihedralGroup.sr i)
    (hs' : weylE S R hp hp2 hζ ⟨s', hs₁⟩ = DihedralGroup.sr j)
    (hpar : i₀.val % 2 = i.val % 2) (hpar' : i₁.val % 2 = j.val % 2)
    (hne : i.val % 2 ≠ j.val % 2) :
    ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G)),
      s = conjAut E x hxE * t₀ * (conjAut E x hxE)⁻¹ ∧
      s' = conjAut E x hxE * t₁ * (conjAut E x hxE)⁻¹ := by
  obtain ⟨w, hw, hw'⟩ := exists_dihedral_conj_pair i₀ i₁ i j hpar hpar' hne
  set u : ↥(torusImage E L) := (weylE S R hp hp2 hζ).symm w with hu
  obtain ⟨x, hxL, hxE, hx⟩ := exists_conjAut_of_mem_torusImage u.2
  refine ⟨x, hxL, hxE, ?_, ?_⟩
  · have h1 : u * ⟨t₀, ht₀⟩ * u⁻¹ = ⟨s, hs₀⟩ := by
      apply (weylE S R hp hp2 hζ).injective
      rw [map_mul, map_mul, map_inv, hu, MulEquiv.apply_symm_apply, h₀, hs, hw]
    have h2 := congrArg (fun y : ↥(torusImage E L) => (y : MulAut E)) h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [← h2, ← hx]
  · have h1 : u * ⟨t₁, ht₁⟩ * u⁻¹ = ⟨s', hs₁⟩ := by
      apply (weylE S R hp hp2 hζ).injective
      rw [map_mul, map_mul, map_inv, hu, MulEquiv.apply_symm_apply, h₁, hs', hw']
    have h2 := congrArg (fun y : ↥(torusImage E L) => (y : MulAut E)) h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [← h2, ← hx]

include S R hp hp2 hζ in
theorem parity_ne_of_pair {s s' : MulAut E} {hs₀ : s ∈ torusImage E L}
    {hs₁ : s' ∈ torusImage E L} {i j : ZMod 4}
    (hs : weylE S R hp hp2 hζ ⟨s, hs₀⟩ = DihedralGroup.sr i)
    (hs' : weylE S R hp hp2 hζ ⟨s', hs₁⟩ = DihedralGroup.sr j)
    (hord : orderOf (s * s') = 4) : i.val % 2 ≠ j.val % 2 := by
  apply parity_ne_of_orderOf_eq_four
  rw [← hs, ← hs', ← map_mul, MulEquiv.orderOf_eq]
  have : orderOf ((⟨s, hs₀⟩ : ↥(torusImage E L)) * ⟨s', hs₁⟩) = orderOf (s * s') := by
    rw [← Subgroup.orderOf_coe]
    rfl
  rw [this]
  exact hord

include S R hp hp2 hζ in
theorem kfAt_of_parity [Finite G] {g : ℕ} {t₀ t : MulAut E} {ht₀ : t₀ ∈ torusImage E L}
    {ht : t ∈ torusImage E L} {i₀ i : ZMod 4}
    (h₀ : weylE S R hp hp2 hζ ⟨t₀, ht₀⟩ = DihedralGroup.sr i₀)
    (h : weylE S R hp hp2 hζ ⟨t, ht⟩ = DihedralGroup.sr i) (hpar : i₀.val % 2 = i.val % 2)
    (hK : KFAt p E g t₀) : KFAt p E g t := by
  obtain ⟨x, hxL, hxE, hx⟩ := exists_conj_of_parity S R hp hp2 hζ h₀ h hpar
  rw [hx]
  exact hK.conj hxE

end Conj

theorem eq_zero_of_sr_fix_one {z : rootsOfUnity p K} (hz1 : z ≠ 1) (hz2 : z ^ 2 ≠ 1) {i : ZMod 4}
    (h : d8Act (p := p) (K := K) (DihedralGroup.sr i) ((1, z) : D8Mod p K) = (1, z)) : i = 0 := by
  have hall : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  have hi := hall i
  rcases hi with rfl | rfl | rfl | rfl
  · rfl
  · exfalso
    rw [d8Act_sr_one] at h
    have h1 := congrArg Prod.fst h
    simp only at h1
    exact hz1 (inv_eq_one.mp h1)
  · exfalso
    rw [d8Act_sr_two] at h
    have h1 := congrArg Prod.snd h
    simp only at h1
    apply hz2
    calc z ^ 2 = z * z := sq z
      _ = z * z⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel z
  · exfalso
    rw [d8Act_sr_three] at h
    have h1 := congrArg Prod.fst h
    simp only at h1
    exact hz1 h1

theorem eq_three_of_sr_fix_same {z : rootsOfUnity p K} (hz2 : z ^ 2 ≠ 1) {i : ZMod 4}
    (h : d8Act (p := p) (K := K) (DihedralGroup.sr i) ((z, z) : D8Mod p K) = (z, z)) : i = 3 := by
  have hall : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  have hi := hall i
  have hinv : z⁻¹ = z → False := by
    intro h1
    apply hz2
    calc z ^ 2 = z * z := sq z
      _ = z * z⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel z
  rcases hi with rfl | rfl | rfl | rfl
  · exfalso
    rw [d8Act_sr_zero] at h
    exact hinv (congrArg Prod.fst h)
  · exfalso
    rw [d8Act_sr_one] at h
    exact hinv (congrArg Prod.fst h)
  · exfalso
    rw [d8Act_sr_two] at h
    exact hinv (congrArg Prod.snd h)
  · rfl

section Fix

variable (S : D8Ctx p K L F) (R : Sec12Three.Restr c L E F) (hp : p.Prime) (hp2 : p ≠ 2)
  (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)

include S R hp hp2 hζ in
theorem weylE_eq_of_fix {t : MulAut E} (ht : t ∈ torusImage E L) (hr : IsAutReflection p E t)
    {d : D8Mod p K} {i₀ : ZMod 4}
    (hfix : ((((t : MulAut E) ⟨((S.tor d : F) : G), R.F_le_E (S.tor d).2⟩ : E)) : G) =
      ((S.tor d : F) : G))
    (hi : ∀ i : ZMod 4, d8Act (p := p) (K := K) (DihedralGroup.sr i) d = d → i = i₀) :
    weylE S R hp hp2 hζ ⟨t, ht⟩ = DihedralGroup.sr i₀ := by
  obtain ⟨i, hi'⟩ := (isAutReflection_weylE_iff S R hp hp2 hζ ⟨t, ht⟩).1 hr
  have h1 := weylE_fix S R hp hp2 hζ ⟨t, ht⟩ d hfix
  rw [hi'] at h1
  rw [hi', hi i h1]

end Fix

end CFSG.RankThree.PartOne.KF132
