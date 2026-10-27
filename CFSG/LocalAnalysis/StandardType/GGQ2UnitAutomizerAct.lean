module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitNormalizerStatements

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open (IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {G : Type} [Group G] [Finite G] {H E : Subgroup G} {R : Type} [Group R]

omit [Finite G] in
private lemma uaa_not_dvd_card_center
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) :
    ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥H) := by
  intro h3
  apply hC3
  have hmap : (Subgroup.center ↥H).map H.subtype ≤ Subgroup.centralizer (H : Set G) := by
    rintro z ⟨h, hh, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hh) ⟨y, hy⟩)
  have hdvd : Nat.card ↥(Subgroup.center ↥H) ∣
      Nat.card ↥(Subgroup.centralizer (H : Set G)) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    exact Subgroup.card_dvd_of_le hmap
  exact h3.trans hdvd

omit [Finite G] in
private lemma uaa_mem_centralizer_of_pi_eq (π : ↥H →* R)
    (hker : π.ker ≤ Subgroup.center ↥H) (hperf : commutator H = ⊤)
    {u : G} (hu : u ∈ Subgroup.normalizer (H : Set G))
    (hact : ∀ h : ↥H, π (H.normalizerMonoidHom ⟨u, hu⟩ h) = π h) :
    u ∈ Subgroup.centralizer (H : Set G) := by
  set c := H.normalizerMonoidHom ⟨u, hu⟩ with hc_def
  have hz : ∀ l : ↥H, c l * l⁻¹ ∈ Subgroup.center ↥H := by
    intro l
    apply hker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hact l, mul_inv_cancel]
  let f : ↥H →* ↥H :=
    { toFun := fun l => c l * l⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have h := (Subgroup.mem_center_iff.mp (hz b)) a⁻¹
        simp only [map_mul, mul_inv_rev]
        calc c a * c b * (b⁻¹ * a⁻¹) = c a * ((c b * b⁻¹) * a⁻¹) := by group
          _ = c a * (a⁻¹ * (c b * b⁻¹)) := by rw [h]
          _ = c a * a⁻¹ * (c b * b⁻¹) := by group }
  have hkerf : commutator H ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hz b)) (f a)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : f ⟨y, hy⟩ = 1 := hkerf (by rw [hperf]; exact Subgroup.mem_top _)
  have h2 : c ⟨y, hy⟩ = ⟨y, hy⟩ := mul_inv_eq_one.mp h1
  have h3 : u * y * u⁻¹ = y := congrArg Subtype.val h2
  calc y * u = (u * y * u⁻¹) * u := by rw [h3]
    _ = u * y := by group

omit [Finite G] in
private lemma uaa_conjHom_apply (x z : ↥H) :
    H.normalizerMonoidHom ⟨(x : G), H.le_normalizer x.2⟩ z = x * z * x⁻¹ := by
  ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  simp

omit [Finite G] in
private lemma uaa_conjHom_inv_apply (x z : ↥H) :
    (H.normalizerMonoidHom ⟨(x : G), H.le_normalizer x.2⟩)⁻¹ z = x⁻¹ * z * x := by
  have h : H.normalizerMonoidHom ⟨(x : G), H.le_normalizer x.2⟩ (x⁻¹ * z * x) = z := by
    rw [uaa_conjHom_apply]
    group
  calc (H.normalizerMonoidHom ⟨(x : G), H.le_normalizer x.2⟩)⁻¹ z
      = (H.normalizerMonoidHom ⟨(x : G), H.le_normalizer x.2⟩)⁻¹
          (H.normalizerMonoidHom ⟨(x : G), H.le_normalizer x.2⟩ (x⁻¹ * z * x)) := by
        rw [h]
    _ = x⁻¹ * z * x := by simp

omit [Finite G] in
private lemma uaa_rho_conj (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (π : ↥H →* R) (ρ : ↥E →* MulAut R) (hsurj : Function.Surjective π)
    (hρ : ∀ (b : ↥E) (h : ↥H), π (H.normalizerMonoidHom ⟨b, hEN b.2⟩ h) = ρ b (π h))
    {x : ↥H} {b : ↥E} {ψ : MulAut ↥E}
    (hψ : ((ψ b : ↥E) : G) = (x : G) * (b : G) * (x : G)⁻¹) :
    ρ (ψ b) = MulAut.conj (π x) * ρ b * (MulAut.conj (π x))⁻¹ := by
  ext r
  obtain ⟨h, rfl⟩ := hsurj r
  have hcx : ∀ z : ↥H, π (H.normalizerMonoidHom ⟨(x : G), H.le_normalizer x.2⟩ z) =
      MulAut.conj (π x) (π z) := by
    intro z
    rw [uaa_conjHom_apply, map_mul, map_mul, map_inv, MulAut.conj_apply]
  have hcxinv : ∀ z : ↥H,
      π ((H.normalizerMonoidHom ⟨(x : G), H.le_normalizer x.2⟩)⁻¹ z) =
        (MulAut.conj (π x))⁻¹ (π z) := by
    intro z
    rw [uaa_conjHom_inv_apply, map_mul, map_mul, map_inv, MulAut.conj_inv_apply]
  have hcomp : H.normalizerMonoidHom ⟨((ψ b : ↥E) : G), hEN (ψ b).2⟩ h =
      H.normalizerMonoidHom ⟨(x : G), H.le_normalizer x.2⟩
        (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩
          ((H.normalizerMonoidHom ⟨(x : G), H.le_normalizer x.2⟩)⁻¹ h)) := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.normalizerMonoidHom_apply_apply_coe,
      uaa_conjHom_inv_apply]
    rw [hψ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [← hρ (ψ b) h, hcomp, hcx, hρ b, hcxinv]
  rw [MulAut.mul_apply, MulAut.mul_apply]

private def uaa_conjSet (ρ : ↥E →* MulAut R) (π : ↥H →* R) (X : Subgroup ↥H) :
    Subgroup (MulAut ↥E) where
  carrier := {ψ | ∃ y ∈ X.map π, ∀ b : ↥E,
    ρ (ψ b) = MulAut.conj y * ρ b * (MulAut.conj y)⁻¹}
  mul_mem' := by
    rintro ψ ψ' ⟨y, hy, hψ⟩ ⟨y', hy', hψ'⟩
    refine ⟨y * y', (X.map π).mul_mem hy hy', fun b => ?_⟩
    rw [MulAut.mul_apply, hψ, hψ']
    simp only [map_mul]
    group
  one_mem' := by
    refine ⟨1, (X.map π).one_mem, fun b => ?_⟩
    simp only [MulAut.one_apply, map_one, one_mul, inv_one, mul_one]
  inv_mem' := by
    rintro ψ ⟨y, hy, hψ⟩
    refine ⟨y⁻¹, (X.map π).inv_mem hy, fun b => ?_⟩
    have hb := hψ (ψ⁻¹ b)
    simp only [MulAut.apply_inv_self] at hb
    have hcalc : (MulAut.conj y)⁻¹ * ρ b * MulAut.conj y = ρ (ψ⁻¹ b) := by
      rw [hb]
      group
    rw [map_inv]
    simpa using hcalc.symm

omit [Finite G] in
private lemma uaa_mem_conjSet_of_mem_ggAutomizer (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (π : ↥H →* R) (ρ : ↥E →* MulAut R) (hsurj : Function.Surjective π)
    (hρ : ∀ (b : ↥E) (h : ↥H), π (H.normalizerMonoidHom ⟨b, hEN b.2⟩ h) = ρ b (π h))
    {X : Subgroup ↥H} {φ : MulAut ↥E}
    (hφ : φ ∈ ggAutomizer (X.map H.subtype) E) : φ ∈ uaa_conjSet ρ π X := by
  have hS : ggAutomizer (X.map H.subtype) E ≤ uaa_conjSet ρ π X := by
    rw [ggAutomizer, Subgroup.closure_le]
    rintro ψ ⟨g, hg, hgN, hgc⟩
    rw [Subgroup.mem_map] at hg
    obtain ⟨x, hxX, rfl⟩ := hg
    exact ⟨π x, Subgroup.mem_map.mpr ⟨x, hxX, rfl⟩,
      fun b => uaa_rho_conj hEN π ρ hsurj hρ (hgc b)⟩
  exact hS hφ

omit [Finite G] in
private lemma uaa_normalizerMonoidHom_inv_apply {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (z : ↥H) :
    (H.normalizerMonoidHom ⟨g, hg⟩)⁻¹ z =
      H.normalizerMonoidHom ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ z := by
  rw [show (H.normalizerMonoidHom ⟨g, hg⟩)⁻¹ =
      H.normalizerMonoidHom (⟨g, hg⟩⁻¹) from (map_inv _ _).symm]
  rfl

private lemma uaa_mem_X_of_centralizer
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)))
    {X : Subgroup ↥H} {u x' e : G}
    (huC : u ∈ Subgroup.centralizer (H : Set G))
    (hx'X : x' ∈ X.map H.subtype) (he3 : e ^ 3 = 1) (hue : u = x' * e) :
    u ∈ X.map H.subtype := by
  have hx'H : x' ∈ H := by
    obtain ⟨xh, -, hx⟩ := Subgroup.mem_map.mp hx'X
    rw [← hx]
    exact xh.2
  have hcomm : x' * u = u * x' := (Subgroup.mem_centralizer_iff.mp huC) x' hx'H
  have heq : e = x'⁻¹ * u := by rw [hue]; group
  have hcube : u ^ 3 = x' ^ 3 := by
    have h3 : (x'⁻¹ * u) ^ 3 = x'⁻¹ ^ 3 * u ^ 3 :=
      (commute_iff_eq x' u).mpr hcomm |>.inv_left |>.mul_pow 3
    rw [heq] at he3
    rw [h3, inv_pow] at he3
    calc u ^ 3 = x' ^ 3 * ((x' ^ 3)⁻¹ * u ^ 3) := by group
      _ = x' ^ 3 * 1 := by rw [he3]
      _ = x' ^ 3 := mul_one _
  have hu3X : u ^ 3 ∈ X.map H.subtype := by
    rw [hcube]
    exact Subgroup.pow_mem _ hx'X 3
  have hvdC : orderOf u ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) :=
    Subgroup.orderOf_dvd_natCard _ huC
  have h3u : ¬ 3 ∣ orderOf u := fun h => hC3 (h.trans hvdC)
  have hcop : Nat.Coprime 3 (orderOf u) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3u
  have hkop : (orderOf u).gcd 3 = 1 := by
    rw [Nat.gcd_comm]
    exact Nat.coprime_iff_gcd_eq_one.mp hcop
  have hord : orderOf (u ^ 3) = orderOf u := by
    rw [orderOf_pow, hkop, Nat.div_one]
  have hsub : Subgroup.zpowers (u ^ 3) ≤ Subgroup.zpowers u :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers u) 3)
  have hcard : Nat.card ↥(Subgroup.zpowers u) ≤ Nat.card ↥(Subgroup.zpowers (u ^ 3)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers]
    exact le_of_eq hord.symm
  have heq' : Subgroup.zpowers (u ^ 3) = Subgroup.zpowers u :=
    Subgroup.eq_of_le_of_card_ge hsub hcard
  have huZp : u ∈ Subgroup.zpowers (u ^ 3) := heq' ▸ Subgroup.mem_zpowers u
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp huZp
  rw [← hn]
  exact Subgroup.zpow_mem _ hu3X n

omit [Finite G] in
private lemma uaa_u_mem_centralizer (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (π : ↥H →* R) (ρ : ↥E →* MulAut R)
    (hker : π.ker ≤ Subgroup.center ↥H) (hperf : commutator H = ⊤)
    (hρ : ∀ (b : ↥E) (h : ↥H), π (H.normalizerMonoidHom ⟨b, hEN b.2⟩ h) = ρ b (π h))
    {x₀ : ↥H} {φ : MulAut ↥E}
    (hconj : ∀ b : ↥E, ρ (φ b) = MulAut.conj (π x₀) * ρ b * (MulAut.conj (π x₀))⁻¹)
    (b : ↥E) :
    ((x₀ : G) * (b : G) * (x₀ : G)⁻¹ * (φ b : G)⁻¹) ∈
      Subgroup.centralizer (H : Set G) := by
  set u : G := (x₀ : G) * (b : G) * (x₀ : G)⁻¹ * (φ b : G)⁻¹ with hu_def
  have huN : u ∈ Subgroup.normalizer (H : Set G) := by
    rw [hu_def]
    apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · apply Subgroup.mul_mem
        · exact H.le_normalizer x₀.2
        · exact hEN b.2
      · exact Subgroup.inv_mem _ (H.le_normalizer x₀.2)
    · exact Subgroup.inv_mem _ (hEN (φ b).2)
  have hact : ∀ h : ↥H, π (H.normalizerMonoidHom ⟨u, huN⟩ h) = π h := by
    intro h
    have hcx : ∀ z : ↥H, π (H.normalizerMonoidHom ⟨(x₀ : G), H.le_normalizer x₀.2⟩ z) =
        MulAut.conj (π x₀) (π z) := by
      intro z
      rw [uaa_conjHom_apply, map_mul, map_mul, map_inv, MulAut.conj_apply]
    have hcxinv : ∀ z : ↥H,
        π ((H.normalizerMonoidHom ⟨(x₀ : G), H.le_normalizer x₀.2⟩)⁻¹ z) =
          (MulAut.conj (π x₀))⁻¹ (π z) := by
      intro z
      rw [uaa_conjHom_inv_apply, map_mul, map_mul, map_inv, MulAut.conj_inv_apply]
    have hφinv : ∀ z : ↥H,
        π ((H.normalizerMonoidHom ⟨(φ b : G), hEN (φ b).2⟩)⁻¹ z) =
          (ρ (φ b))⁻¹ (π z) := by
      intro z
      have h := hρ (φ b) ((H.normalizerMonoidHom ⟨(φ b : G), hEN (φ b).2⟩)⁻¹ z)
      rw [MulAut.apply_inv_self] at h
      calc π ((H.normalizerMonoidHom ⟨(φ b : G), hEN (φ b).2⟩)⁻¹ z)
          = (ρ (φ b))⁻¹ (ρ (φ b) (π ((H.normalizerMonoidHom ⟨(φ b : G),
              hEN (φ b).2⟩)⁻¹ z))) := by simp
        _ = (ρ (φ b))⁻¹ (π z) := by rw [← h]
    have hcomp : H.normalizerMonoidHom ⟨u, huN⟩ h =
        H.normalizerMonoidHom ⟨(x₀ : G), H.le_normalizer x₀.2⟩
          (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩
            ((H.normalizerMonoidHom ⟨(x₀ : G), H.le_normalizer x₀.2⟩)⁻¹
              ((H.normalizerMonoidHom ⟨(φ b : G), hEN (φ b).2⟩)⁻¹ h))) := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe,
        Subgroup.normalizerMonoidHom_apply_apply_coe,
        Subgroup.normalizerMonoidHom_apply_apply_coe,
        uaa_conjHom_inv_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [uaa_normalizerMonoidHom_inv_apply,
        Subgroup.normalizerMonoidHom_apply_apply_coe]
      rw [hu_def]
      group
    rw [hcomp, hcx, hρ b, hcxinv, hφinv]
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← MulAut.mul_apply]
    have hprod : MulAut.conj (π x₀) * ρ b * (MulAut.conj (π x₀))⁻¹ *
        (ρ (φ b))⁻¹ = 1 := by
      rw [hconj b]
      group
    rw [hprod, MulAut.one_apply]
  exact uaa_mem_centralizer_of_pi_eq π hker hperf huN hact

private def uaa_conjOnH (hEN : E ≤ Subgroup.normalizer (H : Set G)) : ↥E →* MulAut ↥H :=
  H.normalizerMonoidHom.comp (Subgroup.inclusion hEN)

private def uaa_W (X : Subgroup ↥H) : Subgroup ↥H := Subgroup.center ↥H ⊓ X

omit [Finite G] in
private lemma uaa_conjOnH_apply (hEN : E ≤ Subgroup.normalizer (H : Set G)) (b : ↥E)
    (x : ↥H) : uaa_conjOnH hEN b x = H.normalizerMonoidHom ⟨b, hEN b.2⟩ x := rfl

omit [Finite G] in
private lemma uaa_conjOnH_mem_center (hEN : E ≤ Subgroup.normalizer (H : Set G)) (b : ↥E)
    {x : ↥H} (hx : x ∈ Subgroup.center ↥H) :
    uaa_conjOnH hEN b x ∈ Subgroup.center ↥H := by
  have hmap : (Subgroup.center ↥H).map (uaa_conjOnH hEN b) = Subgroup.center ↥H :=
    Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : Subgroup.Characteristic (Subgroup.center ↥H)) (uaa_conjOnH hEN b)
  have hmem : uaa_conjOnH hEN b x ∈ (Subgroup.center ↥H).map (uaa_conjOnH hEN b) :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rwa [hmap] at hmem

omit [Finite G] in
private lemma uaa_conjOnH_mem_X {X : Subgroup ↥H}
    (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (hXE : ∀ (b : ↥E) (x : ↥H), x ∈ X →
      H.normalizerMonoidHom ⟨b, hEN b.2⟩ x ∈ X) (b : ↥E) {x : ↥H} (hx : x ∈ X) :
    uaa_conjOnH hEN b x ∈ X := by
  rw [uaa_conjOnH_apply]
  exact hXE b x hx

omit [Finite G] in
private lemma uaa_uaaW_stable {X : Subgroup ↥H}
    (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (hXE : ∀ (b : ↥E) (x : ↥H), x ∈ X →
      H.normalizerMonoidHom ⟨b, hEN b.2⟩ x ∈ X) (b : ↥E) (x : ↥H) :
    x ∈ uaa_W X ↔ uaa_conjOnH hEN b x ∈ uaa_W X := by
  constructor
  · intro hx
    exact Subgroup.mem_inf.mpr
      ⟨uaa_conjOnH_mem_center hEN b (Subgroup.mem_inf.mp hx).1,
        uaa_conjOnH_mem_X hEN hXE b (Subgroup.mem_inf.mp hx).2⟩
  · intro hx
    have h1 : uaa_conjOnH hEN b⁻¹ (uaa_conjOnH hEN b x) ∈ uaa_W X :=
      Subgroup.mem_inf.mpr
        ⟨uaa_conjOnH_mem_center hEN b⁻¹ (Subgroup.mem_inf.mp hx).1,
          uaa_conjOnH_mem_X hEN hXE b⁻¹ (Subgroup.mem_inf.mp hx).2⟩
    have h2 : uaa_conjOnH hEN b⁻¹ (uaa_conjOnH hEN b x) = x := by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    rwa [h2] at h1

omit [Finite G] in
private lemma uaa_E_le_normalizer_map {X : Subgroup ↥H}
    (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (hXE : ∀ (b : ↥E) (x : ↥H), x ∈ X →
      H.normalizerMonoidHom ⟨b, hEN b.2⟩ x ∈ X) :
    E ≤ Subgroup.normalizer (((uaa_W X).map H.subtype : Subgroup G) : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    exact Subgroup.mem_map.mpr
      ⟨uaa_conjOnH hEN ⟨b, hb⟩ w, (uaa_uaaW_stable hEN hXE ⟨b, hb⟩ w).mp hw,
        Subgroup.normalizerMonoidHom_apply_apply_coe H ⟨b, hEN hb⟩ w⟩
  · intro hz
    obtain ⟨w, hw, hw_eq⟩ := Subgroup.mem_map.mp hz
    have hstab : uaa_conjOnH hEN (⟨b, hb⟩ : ↥E)⁻¹ w ∈ uaa_W X :=
      (uaa_uaaW_stable hEN hXE (⟨b, hb⟩ : ↥E)⁻¹ w).mp hw
    have hz_eq : z = ((uaa_conjOnH hEN (⟨b, hb⟩ : ↥E)⁻¹ w : ↥H) : G) := by
      rw [uaa_conjOnH_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        Subgroup.coe_inv]
      change z = b⁻¹ * (H.subtype w) * (b⁻¹)⁻¹
      rw [hw_eq]
      group
    rw [hz_eq]
    exact Subgroup.mem_map.mpr ⟨uaa_conjOnH hEN (⟨b, hb⟩ : ↥E)⁻¹ w, hstab, rfl⟩

private lemma uaa_average {E Z : Type*} [Group E] [Fintype E] [CommGroup Z] [Fintype Z]
    (σ : E →* MulAut Z) (hcop : Nat.Coprime (Nat.card Z) (Nat.card E)) (u : E → Z)
    (hco : ∀ a b : E, u (a * b) = u a * σ a (u b)) :
    ∃ k : Z, ∀ b : E, u b = k * (σ b k)⁻¹ := by
  classical
  let m := Nat.card E
  have hkey : ∀ x : Z, (powCoprime hcop) x = x ^ m := fun x => powCoprime_apply hcop x
  have hsurj : Function.Surjective (fun x : Z => x ^ m) := by
    intro y
    obtain ⟨x, hx⟩ := (powCoprime hcop).surjective y
    refine ⟨x, ?_⟩
    show x ^ m = y
    rw [← hkey]
    exact hx
  have hinj : Function.Injective (fun x : Z => x ^ m) := by
    intro x y hxy
    apply (powCoprime hcop).injective
    rw [hkey, hkey]
    exact hxy
  let s : Z := ∏ c : E, u c
  obtain ⟨k, hk⟩ := hsurj s
  refine ⟨k, fun b => ?_⟩
  have hsb : s = (u b) ^ m * σ b s := by
    have h1 : (∏ c : E, u (b * c)) = ∏ c : E, u c :=
      Fintype.prod_equiv (Equiv.mulLeft b) _ _ (fun c => rfl)
    have h2 : (∏ c : E, u (b * c)) = ∏ c : E, (u b * σ b (u c)) := by
      apply Finset.prod_congr rfl
      intro c _
      exact hco b c
    have h3 : (∏ c : E, (u b * σ b (u c))) = (u b) ^ m * σ b s := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      rw [show Fintype.card E = m from (Nat.card_eq_fintype_card).symm]
      rw [show (∏ c : E, σ b (u c)) = σ b s from by
        rw [map_prod (σ b) u Finset.univ]]
    calc s = ∏ c : E, u c := rfl
      _ = ∏ c : E, u (b * c) := h1.symm
      _ = ∏ c : E, (u b * σ b (u c)) := h2
      _ = (u b) ^ m * σ b s := h3
  have h1 : (u b) ^ m = s * (σ b s)⁻¹ := by
    have hh := congrArg (fun z => z * (σ b s)⁻¹) hsb
    simpa [mul_assoc] using hh.symm
  have hbm : (u b) ^ m = (k * (σ b k)⁻¹) ^ m := by
    calc (u b) ^ m = s * (σ b s)⁻¹ := h1
      _ = k ^ m * (σ b (k ^ m))⁻¹ := by rw [← hk]
      _ = k ^ m * ((σ b k) ^ m)⁻¹ := by rw [map_pow]
      _ = k ^ m * ((σ b k)⁻¹) ^ m := by rw [inv_pow]
      _ = (k * (σ b k)⁻¹) ^ m := (mul_pow _ _ m).symm
  exact hinj hbm

theorem automizerActEq_holds : AutomizerActEq := by
  intro G _ _ H E R _ hEN π ρ hsurj hker hperf hEab hC3 hρ X hXE φ
  classical
  constructor
  · intro hφ
    exact uaa_mem_conjSet_of_mem_ggAutomizer hEN π ρ hsurj hρ hφ
  · rintro ⟨y, hy, hconj⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Subgroup.mem_map] at hy
    obtain ⟨x₀, hx₀X, rfl⟩ := hy
    let u : ↥E → G := fun b => (x₀ : G) * (b : G) * (x₀ : G)⁻¹ * (φ b : G)⁻¹
    have huC : ∀ b : ↥E, u b ∈ Subgroup.centralizer (H : Set G) := fun b =>
      uaa_u_mem_centralizer hEN π ρ hker hperf hρ hconj b
    have hx'X : ∀ b : ↥E,
        (x₀ : G) * ((b : G) * (x₀ : G)⁻¹ * (b : G)⁻¹) ∈ X.map H.subtype := by
      intro b
      refine Subgroup.mem_map.mpr ⟨x₀ * uaa_conjOnH hEN b x₀⁻¹,
        X.mul_mem hx₀X (hXE b x₀⁻¹ (X.inv_mem hx₀X)), ?_⟩
      show (x₀ : G) * ((uaa_conjOnH hEN b x₀⁻¹ : ↥H) : G) =
        (x₀ : G) * ((b : G) * ((x₀⁻¹ : ↥H) : G) * (b : G)⁻¹)
      rw [uaa_conjOnH_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have he3 : ∀ b : ↥E, ((b : G) * (φ b : G)⁻¹) ^ 3 = 1 := by
      intro b
      have hb3 : b ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hEab.2 (b : G) b.2
      have hφb3 : (φ b) ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hEab.2 ((φ b : ↥E) : G) (φ b).2
      have hcomm : Commute b ((φ b)⁻¹ : ↥E) :=
        (commute_iff_eq b ((φ b)⁻¹)).mpr (hEab.1.is_comm.comm b ((φ b)⁻¹))
      have h : (b * (φ b)⁻¹ : ↥E) ^ 3 = 1 := by
        rw [hcomm.mul_pow 3, hb3, inv_pow, hφb3, inv_one, mul_one]
      have h' := congrArg (fun z : ↥E => (z : G)) h
      simpa using h'
    have hue : ∀ b : ↥E, u b =
        (x₀ : G) * ((b : G) * (x₀ : G)⁻¹ * (b : G)⁻¹) * ((b : G) * (φ b : G)⁻¹) := by
      intro b
      simp only [u]
      group
    have huX : ∀ b : ↥E, u b ∈ X.map H.subtype := fun b =>
      uaa_mem_X_of_centralizer hC3 (huC b) (hx'X b) (he3 b) (hue b)
    have huH : ∀ b : ↥E, u b ∈ H := by
      intro b
      obtain ⟨xh, -, hx⟩ := Subgroup.mem_map.mp (huX b)
      rw [← hx]
      exact xh.2
    let W : Subgroup ↥H := uaa_W X
    let Z : Subgroup G := W.map H.subtype
    have hZ3 : ¬ 3 ∣ Nat.card ↥Z := by
      have hcard : Nat.card ↥Z = Nat.card ↥W :=
        Subgroup.card_map_of_injective H.subtype_injective
      rw [hcard]
      refine fun h => uaa_not_dvd_card_center hC3 (h.trans ?_)
      exact Subgroup.card_dvd_of_le inf_le_left
    have hZcomm : IsMulCommutative ↥Z :=
      ⟨⟨fun z w => by
        obtain ⟨zH, hzH, hzHeq⟩ := Subgroup.mem_map.mp z.2
        obtain ⟨wH, hwH, hwHeq⟩ := Subgroup.mem_map.mp w.2
        have hcw := congrArg Subtype.val
          ((Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hzH).1) wH)
        apply Subtype.ext
        change (z : G) * (w : G) = (w : G) * (z : G)
        rw [← hzHeq, ← hwHeq]
        exact hcw.symm⟩⟩
    have : IsMulCommutative ↥Z := hZcomm
    let : CommGroup ↥Z := IsMulCommutative.instCommGroup
    have hEZ : E ≤ Subgroup.normalizer (Z : Set G) := uaa_E_le_normalizer_map hEN hXE
    let σ : ↥E →* MulAut ↥Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hEZ)
    let τ : ↥E →* MulAut ↥Z := σ.comp φ.toMonoidHom
    have huZ : ∀ b : ↥E, u b ∈ Z := by
      intro b
      let uH : ↥H := ⟨u b, huH b⟩
      have huHcenter : uH ∈ Subgroup.center ↥H := by
        rw [Subgroup.mem_center_iff]
        intro z
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp (huC b)) (z : G) z.2
      have huHX : uH ∈ X := by
        obtain ⟨xh, hxX, hxeq⟩ := Subgroup.mem_map.mp (huX b)
        have hxu : xh = uH := Subtype.ext (hxeq.trans rfl)
        rwa [hxu] at hxX
      exact Subgroup.mem_map.mpr ⟨uH, Subgroup.mem_inf.mpr ⟨huHcenter, huHX⟩, rfl⟩
    let uZ : ↥E → ↥Z := fun b => ⟨u b, huZ b⟩
    have hcocycle : ∀ b₁ b₂ : ↥E, uZ (b₁ * b₂) = uZ b₁ * τ b₁ (uZ b₂) := by
      intro b₁ b₂
      apply Subtype.ext
      show u (b₁ * b₂) = u b₁ * ((τ b₁ (uZ b₂) : ↥Z) : G)
      have hτ : ((τ b₁ (uZ b₂) : ↥Z) : G) =
          (φ b₁ : G) * u b₂ * (φ b₁ : G)⁻¹ := by
        change ((Z.normalizerMonoidHom ⟨((φ b₁ : ↥E) : G), hEZ (φ b₁).2⟩
          (uZ b₂) : ↥Z) : G) = _
        exact Subgroup.normalizerMonoidHom_apply_apply_coe Z
          ⟨((φ b₁ : ↥E) : G), hEZ (φ b₁).2⟩ (uZ b₂)
      rw [hτ]
      show (x₀ : G) * ((b₁ * b₂ : ↥E) : G) * (x₀ : G)⁻¹ * (φ (b₁ * b₂) : G)⁻¹ =
        (x₀ : G) * (b₁ : G) * (x₀ : G)⁻¹ * (φ b₁ : G)⁻¹ *
          ((φ b₁ : G) * ((x₀ : G) * (b₂ : G) * (x₀ : G)⁻¹ * (φ b₂ : G)⁻¹) *
            (φ b₁ : G)⁻¹)
      rw [map_mul]
      simp only [Subgroup.coe_mul]
      group
    have hE3 : IsPGroup 3 ↥E := by
      rw [IsPGroup.iff_orderOf]
      intro b
      have hb3 : (b : G) ^ 3 = 1 := hEab.2 b b.2
      have hdvd3 : orderOf (b : G) ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
      have hord : orderOf b = orderOf (b : G) :=
        (orderOf_injective E.subtype E.subtype_injective b).symm
      rw [hord]
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
      · exact ⟨0, by rw [h1]; simp⟩
      · exact ⟨1, by rw [h3]; simp⟩
    obtain ⟨nE, hnE⟩ := (IsPGroup.iff_card).mp hE3
    have hcop : Nat.Coprime (Nat.card ↥Z) (Nat.card ↥E) := by
      have hc3 : Nat.Coprime 3 (Nat.card ↥Z) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ3
      have hc : Nat.Coprime (Nat.card ↥Z) (3 ^ nE) := (hc3.pow_left nE).symm
      rw [hnE]
      exact hc
    have : Fintype ↥E := Fintype.ofFinite _
    have : Fintype ↥Z := Fintype.ofFinite _
    obtain ⟨k, hk⟩ := uaa_average τ hcop uZ hcocycle
    have hxconj : ∀ b : ↥E,
        (x₀ : G) * (b : G) * (x₀ : G)⁻¹ = (k : G) * (φ b : G) * (k : G)⁻¹ := by
      intro b
      have h1G : u b = (k : G) * ((φ b : G) * (k : G) * (φ b : G)⁻¹)⁻¹ := by
        have h1' : (uZ b : G) = ((k * (τ b k)⁻¹ : ↥Z) : G) :=
          congrArg (fun z : ↥Z => (z : G)) (hk b)
        have h1'' : u b = (k : G) * ((τ b k : ↥Z) : G)⁻¹ := by
          simpa [uZ, Subgroup.coe_mul, Subgroup.coe_inv] using h1'
        have hτb : ((τ b k : ↥Z) : G) = (φ b : G) * (k : G) * (φ b : G)⁻¹ := by
          change ((Z.normalizerMonoidHom ⟨((φ b : ↥E) : G), hEZ (φ b).2⟩ k : ↥Z) : G) = _
          exact Subgroup.normalizerMonoidHom_apply_apply_coe Z
            ⟨((φ b : ↥E) : G), hEZ (φ b).2⟩ k
        rw [h1'', hτb]
      have h2 : (x₀ : G) * (b : G) * (x₀ : G)⁻¹ * (φ b : G)⁻¹ =
          (k : G) * ((φ b : G) * (k : G) * (φ b : G)⁻¹)⁻¹ := by
        rw [← h1G]
      calc (x₀ : G) * (b : G) * (x₀ : G)⁻¹
          = ((x₀ : G) * (b : G) * (x₀ : G)⁻¹ * (φ b : G)⁻¹) * (φ b : G) := by group
        _ = ((k : G) * ((φ b : G) * (k : G) * (φ b : G)⁻¹)⁻¹) * (φ b : G) := by rw [h2]
        _ = (k : G) * (φ b : G) * (k : G)⁻¹ := by group
    have hZleX : Z ≤ X.map H.subtype := Subgroup.map_mono inf_le_right
    have hkX : (k : G) ∈ X.map H.subtype := hZleX k.2
    have hxX : (k : G)⁻¹ * (x₀ : G) ∈ X.map H.subtype :=
      (X.map H.subtype).mul_mem ((X.map H.subtype).inv_mem hkX)
        (Subgroup.mem_map.mpr ⟨x₀, hx₀X, rfl⟩)
    have hxconjG : ∀ b : ↥E,
        (k : G)⁻¹ * (x₀ : G) * (b : G) * ((k : G)⁻¹ * (x₀ : G))⁻¹ = (φ b : G) := by
      intro b
      calc (k : G)⁻¹ * (x₀ : G) * (b : G) * ((k : G)⁻¹ * (x₀ : G))⁻¹
          = (k : G)⁻¹ * ((x₀ : G) * (b : G) * (x₀ : G)⁻¹) * (k : G) := by group
        _ = (k : G)⁻¹ * ((k : G) * (φ b : G) * (k : G)⁻¹) * (k : G) := by rw [hxconj b]
        _ = (φ b : G) := by group
    have hxN : (k : G)⁻¹ * (x₀ : G) ∈ Subgroup.normalizer (E : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro b
      constructor
      · intro hb
        rw [hxconjG ⟨b, hb⟩]
        exact (φ ⟨b, hb⟩).2
      · intro hb
        let e : ↥E := ⟨(k : G)⁻¹ * (x₀ : G) * b * ((k : G)⁻¹ * (x₀ : G))⁻¹, hb⟩
        have h := hxconjG (φ.symm e)
        have he : ((φ (φ.symm e) : ↥E) : G) = (e : G) :=
          congrArg (fun z : ↥E => (z : G)) (φ.apply_symm_apply e)
        rw [he] at h
        have hb_eq : ((φ.symm e : ↥E) : G) = b := by
          have hx_eq : (k : G)⁻¹ * (x₀ : G) * ((φ.symm e : ↥E) : G) *
              ((k : G)⁻¹ * (x₀ : G))⁻¹ =
              (k : G)⁻¹ * (x₀ : G) * b * ((k : G)⁻¹ * (x₀ : G))⁻¹ := by
            rw [h]
          calc ((φ.symm e : ↥E) : G)
              = ((k : G)⁻¹ * (x₀ : G))⁻¹ *
                  ((k : G)⁻¹ * (x₀ : G) * ((φ.symm e : ↥E) : G) *
                    ((k : G)⁻¹ * (x₀ : G))⁻¹) * ((k : G)⁻¹ * (x₀ : G)) := by group
            _ = ((k : G)⁻¹ * (x₀ : G))⁻¹ *
                  ((k : G)⁻¹ * (x₀ : G) * b * ((k : G)⁻¹ * (x₀ : G))⁻¹) *
                  ((k : G)⁻¹ * (x₀ : G)) := by rw [hx_eq]
            _ = b := by group
        rw [← hb_eq]
        exact (φ.symm e).2
    refine Subgroup.subset_closure ⟨(k : G)⁻¹ * (x₀ : G), hxX, hxN, ?_⟩
    intro b
    exact (hxconjG b).symm

end

end CFSG.StandardType.GGQ2Frame.UnitPlacement
