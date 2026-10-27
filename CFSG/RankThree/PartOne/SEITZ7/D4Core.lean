module

public import CFSG.RankThree.PartOne.SEITZ7.D4Close
public import CFSG.RankThree.PartOne.SEITZ7.D4MaxGold
public import CFSG.RankThree.PartOne.SEITZ6.G2Core
public import CFSG.RankThree.PartOne.SEITZ7.D4BrN

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.RankThree.PartOne.CTP
open scoped commutatorElement

theorem two_elt_abstract {G : Type*} [Group G] {T U : Subgroup G}
    (hn : ∀ t ∈ T, ∀ v ∈ U, t * v * t⁻¹ ∈ U) (hodd : ∀ t ∈ T, Odd (orderOf t))
    (hsq : ∀ v ∈ U, v ^ 2 = 1) {t u : G} (ht : t ∈ T) (hu : u ∈ U) {k : ℕ}
    (hk : (t * u) ^ (2 ^ k) = 1) : t = 1 := by
  have hpow : ∀ j : ℕ, ∃ v ∈ U, (t * u) ^ j = t ^ j * v := by
    intro j
    induction j with
    | zero => exact ⟨1, U.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨v, hv, hvj⟩ := ih
      refine ⟨(t⁻¹ * v * t) * u, U.mul_mem ?_ hu, ?_⟩
      · have := hn t⁻¹ (T.inv_mem ht) v hv
        simpa using this
      · rw [pow_succ, hvj]
        group
  obtain ⟨v, hv, hvk⟩ := hpow (2 ^ k)
  rw [hk] at hvk
  have h1 : t ^ (2 ^ k) = v⁻¹ := eq_inv_of_mul_eq_one_left hvk.symm
  have h2 : (t ^ (2 ^ k)) ^ 2 = 1 := by
    rw [h1]
    exact hsq _ (U.inv_mem hv)
  rw [← pow_mul] at h2
  have h3 : orderOf t ∣ 2 ^ (k + 1) := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_succ]
    exact h2
  obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h3
  have hodd' := hodd t ht
  have hi0 : i = 0 := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact h
    · exfalso
      rw [hio] at hodd'
      exact (Nat.not_odd_iff_even.2 ((Nat.even_pow' h.ne').2 even_two)) hodd'
  rw [hi0, pow_zero] at hio
  exact orderOf_eq_one_iff.1 hio

variable {K : Type} [Field K] {σ : K →+* K}

theorem xA_zero [CharP K 2] : xA σ (0 : K) = 1 := by
  simp [xA, xd_zero]

theorem xA_add [CharP K 2] (σ : K →+* K) (a b : K) : xA σ (a + b) = xA σ a * xA σ b := by
  have e : ∀ c : K, xA σ c = xOrbit σ (d4Root 0) c := fun c =>
    (xOrbit_eq σ rho_dict.2.2.2.1 rho_dict.2.2.2.2.1 c).symm
  rw [e, e, e]
  exact xOrbit_add σ (isRoot_d4 (by norm_num : 0 < 24)) rho_ne_dict.1 a b

theorem xA_mul_self [CharP K 2] (σ : K →+* K) (a : K) : xA σ a * xA σ a = 1 := by
  rw [← xA_add, CharTwo.add_self_eq_zero, xA_zero]

theorem Upt_sq [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {g : adjointGroup d4 K}
    (hg : g ∈ Upt σ) : g ^ 2 = 1 := by
  obtain ⟨a, b, -, rfl⟩ := (mem_Upt_iff hσ).1 hg
  have hc : Commute (xH a) (xA σ b) := commute_xH_xA σ a b
  rw [hc.mul_pow, pow_two, pow_two, xA_mul_self, show xH a * xH a = 1 from xd_mul_self 22 a,
    mul_one]

theorem mem_Tt_form {t : twistedGroup σ} (ht : t ∈ ⨆ i, hHat σ i) :
    ∃ s u : Kˣ, σ (s : K) = (s : K) ∧
      (t : adjointGroup d4 K) = torusElement d4 K (nd 2) s * hShortHom σ u := by
  have hcomm : ∀ (s : Kˣ) (u : Kˣ), torusElement d4 K (nd 2) s * hShortHom σ u =
      hShortHom σ u * torusElement d4 K (nd 2) s := by
    intro s u
    rw [hShortHom_apply]
    exact ((torusElement_commute (nd 2) (nd 0) s u).mul_right
      (torusElement_commute (nd 2) (nd 1) s (Units.map σ.toMonoidHom u))).mul_right
      (torusElement_commute (nd 2) (nd 3) s
        (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom u))) |>.eq
  refine Subgroup.iSup_induction (fun i => hHat σ i) (C := fun t : twistedGroup σ =>
    ∃ s u : Kˣ, σ (s : K) = (s : K) ∧
      (t : adjointGroup d4 K) = torusElement d4 K (nd 2) s * hShortHom σ u) ht ?_ ?_ ?_
  · intro i x hx
    fin_cases i
    · obtain ⟨s, hs⟩ : (x : adjointGroup d4 K) ∈ (hLongHom σ).range := hx
      refine ⟨(s : Kˣ), 1, (mem_fixedUnits σ).1 s.2, ?_⟩
      rw [← hs, map_one, mul_one]
      rfl
    · obtain ⟨u, hu⟩ : (x : adjointGroup d4 K) ∈ (hShortHom σ).range := hx
      refine ⟨1, u, by simp, ?_⟩
      rw [← hu, torusElement_one_d4, one_mul]
  · exact ⟨1, 1, by simp, by simp [torusElement_one_d4]⟩
  · rintro x y ⟨s, u, hs, hx⟩ ⟨s', u', hs', hy⟩
    refine ⟨s * s', u * u', by simp [hs, hs'], ?_⟩
    rw [Subgroup.coe_mul, hx, hy, torusElement_mul_d4, map_mul]
    calc torusElement d4 K (nd 2) s * hShortHom σ u *
          (torusElement d4 K (nd 2) s' * hShortHom σ u') =
        torusElement d4 K (nd 2) s * (hShortHom σ u * torusElement d4 K (nd 2) s') *
          hShortHom σ u' := by group
      _ = _ := by rw [← hcomm s' u]; group

theorem torusElement_pow_d4 (i : Fin d4.rank) (s : Kˣ) (m : ℕ) :
    torusElement d4 K i s ^ m = torusElement d4 K i (s ^ m) :=
  ((torusHom (τ := d4) K i).map_pow s m).symm

theorem Tt_odd_order [CharP K 2] [Finite K] {t : twistedGroup σ} (ht : t ∈ ⨆ i, hHat σ i) :
    Odd (orderOf t) := by
  obtain ⟨s, u, -, hsu⟩ := mem_Tt_form ht
  have hc : Commute (torusElement d4 K (nd 2) s) (hShortHom σ u) := by
    rw [hShortHom_apply]
    exact ((torusElement_commute (nd 2) (nd 0) s u).mul_right
      (torusElement_commute (nd 2) (nd 1) s (Units.map σ.toMonoidHom u))).mul_right
      (torusElement_commute (nd 2) (nd 3) s
        (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom u)))
  have h : t ^ (Nat.card K - 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hsu, hc.mul_pow, torusElement_pow_d4, ← map_pow,
      SEITZ6.unit_pow_card_sub_one, SEITZ6.unit_pow_card_sub_one, torusElement_one_d4, map_one,
      mul_one]
    rfl
  exact Odd.of_dvd_nat SEITZ6.card_sub_one_odd (orderOf_dvd_of_pow_eq_one h)

@[expose] noncomputable def Tt (σ : K →+* K) : Subgroup (twistedGroup σ) := ⨆ i, hHat σ i

@[expose] noncomputable def UptG (σ : K →+* K) : Subgroup (twistedGroup σ) :=
  (Upt σ).subgroupOf (twistedGroup σ)

theorem sl2Upper_eq_u2 {k : Type} [Field k] (c : k) : sl2Upper c = u2 c :=
  Subtype.ext (by rw [u2_coe]; rfl)

theorem Tt_le_Lsub [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) : Tt σ ≤ Lsub σ hσ :=
  iSup_le fun i => hHat_le_Lsub σ hσ i

theorem UptG_eq [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {x : twistedGroup σ}
    (hx : x ∈ UptG σ) : ∃ (a : fixedField σ) (b : K),
      x = slShort σ hσ (sl2Upper b) * psiB σ hσ (sl2Upper a) := by
  obtain ⟨a, b, ha, hab⟩ := (mem_Upt_iff hσ).1 (Subgroup.mem_subgroupOf.1 hx)
  refine ⟨⟨a, ha⟩, b, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, slShort_upper_xA, psiB_upper, hab]
  exact commute_xH_xA σ a b

theorem UptG_le_Lsub [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) : UptG σ ≤ Lsub σ hσ := by
  intro x hx
  obtain ⟨a, b, rfl⟩ := UptG_eq hσ hx
  exact mul_mem (Asub_le_Lsub σ hσ ⟨_, rfl⟩) (Bsub_le_Lsub σ hσ ⟨_, rfl⟩)

@[expose] noncomputable def phiAB [CharP K 2] (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c) :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) →*
      twistedGroup σ :=
  MonoidHom.noncommCoprod (slShort σ hσ) (psiB σ hσ) (fun M N => slShort_commute_psi σ hσ M N)

theorem phiAB_apply [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (M N) :
    phiAB σ hσ (M, N) = slShort σ hσ M * psiB σ hσ N := MonoidHom.noncommCoprod_apply _ _ _ _

theorem phiAB_injective [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    Function.Injective (phiAB σ hσ) := by
  refine (injective_iff_map_eq_one _).2 fun ⟨M, N⟩ h => ?_
  rw [phiAB_apply] at h
  have hmem : slShort σ hσ M ∈ Asub σ hσ ⊓ Bsub σ hσ :=
    ⟨⟨M, rfl⟩, ⟨N⁻¹, by rw [map_inv, eq_inv_of_mul_eq_one_left h]⟩⟩
  rw [Asub_inf_Bsub, Subgroup.mem_bot] at hmem
  have hM : M = 1 := slShort_injective hσ (by rw [hmem, map_one])
  subst hM
  rw [map_one, one_mul] at h
  have hN : N = 1 := psiB_injective σ hσ (by rw [h, map_one])
  rw [hN]
  rfl

theorem range_phiAB [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    (phiAB σ hσ).range = Lsub σ hσ := by
  apply le_antisymm
  · rintro _ ⟨⟨M, N⟩, rfl⟩
    rw [phiAB_apply]
    exact mul_mem (Asub_le_Lsub σ hσ ⟨_, rfl⟩) (Bsub_le_Lsub σ hσ ⟨_, rfl⟩)
  · refine sup_le ?_ ?_
    · rintro _ ⟨M, rfl⟩
      exact ⟨(M, 1), by rw [phiAB_apply, map_one, mul_one]⟩
    · rintro _ ⟨N, rfl⟩
      exact ⟨(1, N), by rw [phiAB_apply, map_one, one_mul]⟩

theorem map_Uup_eq_UptG [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    ((SEITZ6.Uup K).prod (SEITZ6.Uup (fixedField σ))).map (phiAB σ hσ) = UptG σ := by
  ext g
  constructor
  · rintro ⟨⟨x, y⟩, hxy, rfl⟩
    obtain ⟨a, rfl⟩ := SEITZ6.mem_Uup_iff.1 (Subgroup.mem_prod.1 hxy).1
    obtain ⟨b, rfl⟩ := SEITZ6.mem_Uup_iff.1 (Subgroup.mem_prod.1 hxy).2
    rw [phiAB_apply, ← sl2Upper_eq_u2, ← sl2Upper_eq_u2]
    refine Subgroup.mem_subgroupOf.2 ?_
    rw [Subgroup.coe_mul, slShort_upper_xA, psiB_upper]
    refine (mem_Upt_iff hσ).2 ⟨b, a, b.2, ?_⟩
    exact (commute_xH_xA σ b a).symm
  · intro hg
    obtain ⟨a, b, rfl⟩ := UptG_eq hσ hg
    exact ⟨(u2 b, u2 a), Subgroup.mem_prod.2 ⟨SEITZ6.u2_mem_Uup b, SEITZ6.u2_mem_Uup a⟩, by
      rw [phiAB_apply, ← sl2Upper_eq_u2, ← sl2Upper_eq_u2]⟩

theorem odd_normal_trivial_of_sub {G : Type*} [Group G] (H : Subgroup G)
    (hOdd : ∀ R : Subgroup G, R ≤ H → (∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) → Odd (Nat.card R) →
      R = ⊥) : ∀ N : Subgroup H, N.Normal → Odd (Nat.card N) → N = ⊥ := by
  intro N hN hodd
  have hRle : N.map H.subtype ≤ H := fun x ⟨y, _, hy⟩ => hy ▸ y.2
  have hRn : ∀ h ∈ H, ∀ r ∈ N.map H.subtype, h * r * h⁻¹ ∈ N.map H.subtype := by
    rintro h hh r ⟨y, hy, rfl⟩
    exact ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, hN.conj_mem y hy _, rfl⟩
  have hcard : Nat.card (N.map H.subtype) = Nat.card N :=
    Nat.card_congr (N.equivMapOfInjective H.subtype H.subtype_injective).toEquiv.symm
  have := hOdd _ hRle hRn (hcard ▸ hodd)
  exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).1 this

theorem Tt_conj_UptG {t : twistedGroup σ} (ht : t ∈ Tt σ) {v : twistedGroup σ}
    (hv : v ∈ UptG σ) : t * v * t⁻¹ ∈ UptG σ :=
  Subgroup.mem_subgroupOf.2 (Tt_conj_Upt ht (Subgroup.mem_subgroupOf.1 hv))

theorem core_max_tw (hgold : CFSG.Goldschmidt.TopStatement)
    [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (hF : Nat.card (fixedField σ) = 2 ^ n)
    (H : Subgroup (twistedGroup σ)) (hL : Lsub σ hσ ≤ H) (hX : Nat.card H ∣ d4Order n)
    (hOdd : ∀ R : Subgroup (twistedGroup σ), R ≤ H →
      (∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) → Odd (Nat.card R) → R = ⊥) :
    H = Lsub σ hσ ∨ H = ⊤ := by
  by_cases htop : H = ⊤
  · exact Or.inr htop
  left
  have : CharP (fixedField σ) 2 :=
    (RingHom.charP_iff (fixedField σ).subtype (fixedField σ).subtype.injective 2).2 inferInstance
  have hq4 : 4 ≤ 2 ^ n := SEITZ6.four_le_two_pow hn
  have hne : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    have hbij : Function.Bijective (fixedField σ).subtype :=
      ⟨(fixedField σ).subtype.injective, fun a => ⟨⟨a, h a⟩, rfl⟩⟩
    have := Nat.card_congr (Equiv.ofBijective _ hbij)
    rw [hF, hK] at this
    nlinarith [pow_pos (show 0 < 2 ^ n by omega) 2]
  have hb3 : ∀ b : K, σ b = b → (∃ x ∈ H, (x : adjointGroup d4 K) = xN b) → b = 0 :=
    fun b hbσ hx => by
      by_contra hb0
      exact htop (eq_top_of_xN hσ hL hb0 hbσ hx)
  have hNorm : ∀ y : twistedGroup σ, y ∈ H →
      (∀ x ∈ Upt σ, (y : adjointGroup d4 K) * x * (y : adjointGroup d4 K)⁻¹ ∈ Upt σ) →
      ∃ t0 ∈ Tt σ, ∃ u ∈ Upt σ, (y : adjointGroup d4 K) = (t0 : adjointGroup d4 K) * u := by
    intro y hyH hy
    obtain ⟨t0, ht0, a, b, c, hbσ, hcσ, hyeq⟩ := normalizer_Upt_form hσ hne hy
    have hxA : slShort σ hσ (sl2Upper a) ∈ H := hL (Asub_le_Lsub σ hσ ⟨_, rfl⟩)
    have hxH : psiB σ hσ (sl2Upper (⟨c, hcσ⟩ : fixedField σ)) ∈ H :=
      hL (Bsub_le_Lsub σ hσ ⟨_, rfl⟩)
    have ht0H : t0 ∈ H := hL (Tt_le_Lsub hσ ht0)
    have hxN : ∃ x ∈ H, (x : adjointGroup d4 K) = xN b := by
      refine ⟨(slShort σ hσ (sl2Upper a))⁻¹ * (t0⁻¹ * y) *
        (psiB σ hσ (sl2Upper (⟨c, hcσ⟩ : fixedField σ)))⁻¹,
        H.mul_mem (H.mul_mem (H.inv_mem hxA) (H.mul_mem (H.inv_mem ht0H) hyH))
          (H.inv_mem hxH), ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, slShort_upper_xA, psiB_upper, hyeq]
      group
    have hb0 := hb3 b hbσ hxN
    subst hb0
    refine ⟨t0, ht0, xH c * xA σ a, (mem_Upt_iff hσ).2 ⟨c, a, hcσ, rfl⟩, ?_⟩
    rw [hyeq, show xN (0 : K) = 1 from xd_zero 19, mul_one, (commute_xH_xA σ c a)]
  have hphi : ∀ x, phiAB σ hσ x ∈ H := fun x =>
    hL (by rw [← range_phiAB hσ]; exact ⟨x, rfl⟩)
  let φ : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) →*
      H := (phiAB σ hσ).codRestrict H hphi
  have hφinj : Function.Injective φ := fun x y h => phiAB_injective hσ (congrArg Subtype.val h)
  let S0 : Subgroup H := (UptG σ).subgroupOf H
  have hS0eq : S0 = ((SEITZ6.Uup K).prod (SEITZ6.Uup (fixedField σ))).map φ := by
    ext ⟨g, hgH⟩
    constructor
    · intro hg
      have hg' : g ∈ UptG σ := hg
      rw [← map_Uup_eq_UptG hσ] at hg'
      obtain ⟨x, hx, rfl⟩ := hg'
      exact ⟨x, hx, Subtype.ext rfl⟩
    · rintro ⟨x, hx, hxg⟩
      have h1 : g = phiAB σ hσ x := (congrArg Subtype.val hxg).symm
      have h2 : g ∈ UptG σ := by
        rw [h1, ← map_Uup_eq_UptG hσ]
        exact ⟨x, hx, rfl⟩
      exact h2
  have hS0p : IsPGroup 2 S0 := fun g =>
    ⟨1, Subtype.ext (Subtype.ext (Subtype.ext (by
      simpa using Upt_sq hσ (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 g.2)))))⟩
  have hNS0 : ∀ y : H, y ∈ Subgroup.normalizer (S0 : Set H) →
      ∃ t0 ∈ Tt σ, ∃ u ∈ Upt σ,
        ((y : twistedGroup σ) : adjointGroup d4 K) = (t0 : adjointGroup d4 K) * u := by
    intro y hy
    refine hNorm y y.2 fun x hx => ?_
    have hxΓ : x ∈ twistedGroup σ := Upt_le_twistedGroup σ hx
    have hxU : (⟨x, hxΓ⟩ : twistedGroup σ) ∈ UptG σ := Subgroup.mem_subgroupOf.2 hx
    have hxH : (⟨x, hxΓ⟩ : twistedGroup σ) ∈ H := hL (UptG_le_Lsub hσ hxU)
    have := (Subgroup.mem_normalizer_iff.1 hy) ⟨⟨x, hxΓ⟩, hxH⟩
    exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 (this.1 hxU))
  have hN2 : ∀ y : H, y ∈ Subgroup.normalizer (S0 : Set H) → (∃ k : ℕ, y ^ (2 ^ k) = 1) →
      y ∈ S0 := by
    intro y hy ⟨k, hk⟩
    obtain ⟨t0, ht0, u, hu, hyu⟩ := hNS0 y hy
    have huΓ : (⟨u, Upt_le_twistedGroup σ hu⟩ : twistedGroup σ) ∈ UptG σ :=
      Subgroup.mem_subgroupOf.2 hu
    have hyΓ : (y : twistedGroup σ) = t0 * ⟨u, Upt_le_twistedGroup σ hu⟩ := Subtype.ext hyu
    have hkΓ : (t0 * ⟨u, Upt_le_twistedGroup σ hu⟩) ^ (2 ^ k) = 1 := by
      rw [← hyΓ]
      exact congrArg Subtype.val hk
    have ht1 : t0 = 1 := two_elt_abstract (T := Tt σ) (U := UptG σ)
      (fun t ht v hv => Tt_conj_UptG ht hv) (fun t ht => Tt_odd_order ht)
      (fun v hv => Subtype.ext (by
        simpa using Upt_sq hσ (Subgroup.mem_subgroupOf.1 hv))) ht0 huΓ hkΓ
    show (y : twistedGroup σ) ∈ UptG σ
    rw [hyΓ, ht1, one_mul]
    exact huΓ
  let S : Sylow 2 H :=
    { toSubgroup := S0
      isPGroup' := hS0p
      is_maximal' := fun {Q} hQ hle => SEITZ6.sylow_of_normalizer S0 hN2 hQ hle }
  have hNle : Subgroup.normalizer ((S : Subgroup H) : Set H) ≤ φ.range := by
    intro y hy
    obtain ⟨t0, ht0, u, hu, hyu⟩ := hNS0 y hy
    have hmem : (y : twistedGroup σ) ∈ Lsub σ hσ := by
      have : (y : twistedGroup σ) = t0 * ⟨u, Upt_le_twistedGroup σ hu⟩ := Subtype.ext hyu
      rw [this]
      exact mul_mem (Tt_le_Lsub hσ ht0) (UptG_le_Lsub hσ (Subgroup.mem_subgroupOf.2 hu))
    rw [← range_phiAB hσ] at hmem
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, Subtype.ext hx⟩
  have hOH : ∀ N : Subgroup H, N.Normal → Odd (Nat.card N) → N = ⊥ :=
    odd_normal_trivial_of_sub H hOdd
  have hsurj := goldschmidt_finish2 hgold hn hK hF φ hφinj S hS0eq hNle hOH hX
  apply le_antisymm
  · intro h hh
    obtain ⟨x, hx⟩ := hsurj ⟨h, hh⟩
    rw [← range_phiAB hσ]
    exact ⟨x, congrArg Subtype.val hx⟩
  · exact hL

end CFSG.RankThree.PartOne.SEITZ7
