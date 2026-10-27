module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldSylowOmega
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.RankThree.PartOne (omegaOne)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

@[expose] def AutOmegaCentral (X : Type) [Group X] : Prop :=
  ∀ R : Subgroup (MulAut X), IsPGroup 3 R →
    omegaOne 3 (R ⊓ inner X) ≤ (Subgroup.center ↥R).map R.subtype

@[expose] def FieldSylowData (X : Type) [Group X] (b : ℕ) : Prop :=
  ∃ (Q : Sylow 3 X) (τ : MulAut X) (s : ℕ),
    (∀ x ∈ (Q : Subgroup X), ∀ y ∈ (Q : Subgroup X), x * y = y * x) ∧
    s % 3 = 1 ∧ (∀ x ∈ (Q : Subgroup X), τ x = x ^ s) ∧
    τ ^ (3 ^ b) = 1 ∧ ∀ j : ℕ, τ ^ j ∈ inner X → 3 ^ b ∣ j

private theorem omegaOne_le_self {G : Type*} [Group G] (q : ℕ) (K : Subgroup G) :
    omegaOne q K ≤ K :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

private theorem map_omegaOne {H H' : Type} [Group H] [Group H'] (f : H →* H')
    {K : Subgroup H} (hf : Set.InjOn f K) (q : ℕ) :
    (omegaOne q K).map f = omegaOne q (K.map f) := by
  unfold omegaOne
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.mem_map]
  constructor
  · rintro ⟨x, ⟨hxK, hxq⟩, rfl⟩
    exact ⟨⟨x, hxK, rfl⟩, by rw [← map_pow, hxq, map_one]⟩
  · rintro ⟨⟨x, hxK, rfl⟩, hy⟩
    refine ⟨x, ⟨hxK, ?_⟩, rfl⟩
    have h1 : f (x ^ q) = f 1 := by rw [map_pow, hy, map_one]
    exact hf (K.pow_mem hxK q) K.one_mem h1

private theorem mem_center_map_subtype_iff {M : Type*} [Group M] (R : Subgroup M)
    {x : M} :
    x ∈ (Subgroup.center ↥R).map R.subtype ↔ x ∈ R ∧ ∀ r ∈ R, r * x = x * r := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun r hr => ?_⟩
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨r, hr⟩)
    simpa using h1
  · rintro ⟨hxR, hx⟩
    refine ⟨⟨x, hxR⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.mpr fun r => Subtype.ext (hx r.1 r.2)

private theorem conj_eq_conj_iff {H : Type*} [Group H] {a b : H} :
    MulAut.conj a = MulAut.conj b ↔ a * b⁻¹ ∈ Subgroup.center H := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 : a * (b⁻¹ * x * b) * a⁻¹ = x := by
      have hh := congrFun (congrArg DFunLike.coe h) (b⁻¹ * x * b)
      rw [MulAut.conj_apply, MulAut.conj_apply] at hh
      rwa [show b * (b⁻¹ * x * b) * b⁻¹ = x by group] at hh
    have ha : a * b⁻¹ * x = (a * (b⁻¹ * x * b) * a⁻¹) * (a * b⁻¹) := by group
    rw [ha, h1]
  · intro h
    ext x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    have hc := Subgroup.mem_center_iff.mp h (b * x * b⁻¹)
    have ha : a * x * a⁻¹ = (a * b⁻¹) * (b * x * b⁻¹) * (a * b⁻¹)⁻¹ := by group
    rw [ha, ← hc]
    group

private theorem conj_conj {H : Type*} [Group H] (σ : MulAut H) (h : H) :
    σ * MulAut.conj h * σ⁻¹ = MulAut.conj (σ h) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

private theorem ker_conj {X : Type*} [Group X] :
    MonoidHom.ker (MulAut.conj : X →* MulAut X) = Subgroup.center X := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have hx := congrFun (congrArg DFunLike.coe h) x
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    have : g * x = x * g := by
      have := congrArg (fun t : X => t * g) hx
      simpa [mul_assoc] using this
    exact this.symm
  · intro h
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply]
    have := h x
    rw [← this]
    group

private theorem inf_center_eq_bot_of_isPGroup {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {Q : Subgroup X} (hQ : IsPGroup p Q)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center X)) : Q ⊓ Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := hQ ⟨g, hg.1⟩
  have h1 : orderOf g ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by
    have := congrArg (fun z : ↥Q => (z : X)) hk
    simpa using this)
  have h2 : orderOf g ∣ Nat.card (Subgroup.center X) :=
    Subgroup.orderOf_dvd_natCard _ hg.2
  have hcop0 : Nat.Coprime p (Nat.card (Subgroup.center X)) :=
    (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hZ
  have hcop : Nat.Coprime (p ^ k) (Nat.card (Subgroup.center X)) := by
    simpa using Nat.Coprime.pow k 1 hcop0
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

private theorem zpow_mem_inner_eq_one {X : Type} [Group X] {τ : MulAut X} {b : ℕ}
    (horder : orderOf τ = 3 ^ b)
    (hτinner : ∀ j : ℕ, τ ^ j ∈ inner X → 3 ^ b ∣ j)
    {j : ℤ} (hj : τ ^ j ∈ inner X) : τ ^ j = 1 := by
  have hpos : (0 : ℤ) < (orderOf τ : ℤ) := by
    rw [horder]
    positivity
  have hmod : τ ^ (j % (orderOf τ : ℤ)) = τ ^ j := zpow_mod_orderOf τ j
  have hjmod : τ ^ (j % (orderOf τ : ℤ)) ∈ inner X := by
    rw [hmod]
    exact hj
  set r : ℤ := j % (orderOf τ : ℤ) with hr
  have hrn : (r.toNat : ℤ) = r := Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hpos))
  have hrmem : τ ^ r.toNat ∈ inner X := by
    rw [← zpow_natCast, hrn]
    exact hjmod
  have hdvd : 3 ^ b ∣ r.toNat := hτinner r.toNat hrmem
  have hlt : r.toNat < 3 ^ b := by
    have h1 : (r.toNat : ℤ) < (orderOf τ : ℤ) := by
      rw [hrn, hr]
      exact Int.emod_lt_of_pos _ hpos
    rw [horder] at h1
    exact_mod_cast h1
  have hn0 : r.toNat = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
  have hr0 : r = 0 := by
    rw [← hrn, hn0]
    rfl
  calc τ ^ j = τ ^ (j % (orderOf τ : ℤ)) := hmod.symm
    _ = τ ^ r := rfl
    _ = 1 := by rw [hr0, zpow_zero]

theorem autOmegaCentral_of_fieldSylowData {X : Type} [Group X] [Finite X] {b : ℕ}
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center X))
    (hOut : ¬ 3 ^ (b + 1) ∣ Nat.card (Outer X))
    (h : FieldSylowData X b) : AutOmegaCentral X := by
  obtain ⟨Q, τ, s, hQab, hs, hτ, hτorder, hτinner⟩ := h
  let conj : X →* MulAut X := MulAut.conj
  let Qbar : Subgroup (MulAut X) := (Q : Subgroup X).map conj
  have hQbar_le : Qbar ≤ inner X := by
    change (Q : Subgroup X).map conj ≤ inner X
    exact Subgroup.map_le_range conj (Q : Subgroup X)
  have hQinf : (Q : Subgroup X) ⊓ Subgroup.center X = ⊥ :=
    inf_center_eq_bot_of_isPGroup Q.isPGroup' hZ
  have hinjQ : Set.InjOn conj (Q : Set X) := by
    intro a ha b hb hab
    have hmem : a * b⁻¹ ∈ (Q : Subgroup X) ⊓ Subgroup.center X :=
      ⟨(Q : Subgroup X).mul_mem ha ((Q : Subgroup X).inv_mem hb), conj_eq_conj_iff.mp hab⟩
    rw [hQinf, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp hmem
  have hcardQbar : Nat.card Qbar = Nat.card (Q : Subgroup X) := by
    change Nat.card (conj '' (Q : Set X)) = Nat.card (Q : Subgroup X)
    exact Nat.card_image_of_injOn hinjQ
  have hcardQ : Nat.card (Q : Subgroup X) = 3 ^ (Nat.card X).factorization 3 :=
    Sylow.card_eq_multiplicity Q
  have hA : Nat.card (MulAut X) = Nat.card (Outer X) * Nat.card (inner X) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (inner X)
  have hcardX : Nat.card X = Nat.card (inner X) * Nat.card (Subgroup.center X) := by
    have hker : MonoidHom.ker (MulAut.conj : X →* MulAut X) = Subgroup.center X :=
      ker_conj
    have hiso : Nat.card (X ⧸ Subgroup.center X) = Nat.card (inner X) := by
      have := Nat.card_congr
        (QuotientGroup.quotientKerEquivRange (MulAut.conj : X →* MulAut X)).toEquiv
      rw [hker] at this
      exact this
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
    rw [hiso] at this
    exact this
  have hcenter3 : (Nat.card (Subgroup.center X)).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hZ
  have hInnerFactor : (Nat.card (inner X)).factorization 3 = (Nat.card X).factorization 3 := by
    have hmul := Nat.factorization_mul
      (Nat.card_pos (α := ↥(inner X))).ne'
      (Nat.card_pos (α := ↥(Subgroup.center X))).ne'
    have h3 := congrArg (fun f : ℕ →₀ ℕ => f 3) hmul
    simp only [Finsupp.add_apply] at h3
    rw [← hcardX, hcenter3, add_zero] at h3
    exact h3.symm
  have hcardQbarSylow : Nat.card Qbar = 3 ^ (Nat.card (inner X)).factorization 3 := by
    rw [hcardQbar, hcardQ, hInnerFactor]
  have hQbarSylow : IsSylowOf 3 Qbar (inner X) :=
    isSylowOf_of_card hQbar_le hcardQbarSylow
  have hQbarab : ∀ x ∈ Qbar, ∀ y ∈ Qbar, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := hy
    rw [← map_mul, hQab a ha c hc, map_mul]
  have horder_dvd : orderOf τ ∣ 3 ^ b := orderOf_dvd_of_pow_eq_one hτorder
  have hb_dvd : 3 ^ b ∣ orderOf τ := by
    refine hτinner (orderOf τ) ?_
    rw [pow_orderOf_eq_one]
    exact Subgroup.one_mem _
  have horder : orderOf τ = 3 ^ b := Nat.dvd_antisymm horder_dvd hb_dvd
  have hτp : IsPGroup 3 (Subgroup.zpowers τ) :=
    IsPGroup.iff_card.mpr ⟨b, by rw [Nat.card_zpowers, horder]⟩
  have hτI : Subgroup.zpowers τ ⊓ inner X = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz.1
    exact zpow_mem_inner_eq_one horder hτinner hz.2
  have hτbar : ∀ x ∈ Qbar, τ * x * τ⁻¹ = x ^ s := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [conj_conj τ a, hτ a ha, map_pow]
  let π : MulAut X →* Outer X := QuotientGroup.mk' (inner X)
  have hπorder : orderOf (π τ) = 3 ^ b := by
    refine Nat.dvd_antisymm ?_ ?_
    · exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hτorder, map_one])
    · refine hτinner (orderOf (π τ)) ?_
      have : (τ ^ orderOf (π τ) : Outer X) = 1 := by
        simp [π]
      exact (QuotientGroup.eq_one_iff _).mp this
  have hOut_dvd : 3 ^ b ∣ Nat.card (Outer X) := by
    have := orderOf_dvd_natCard (π τ)
    rwa [hπorder] at this
  have hOutFactor : (Nat.card (Outer X)).factorization 3 = b := by
    have hn : Nat.card (Outer X) ≠ 0 := (Nat.card_pos (α := Outer X)).ne'
    have h1 : b ≤ (Nat.card (Outer X)).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hn).mp hOut_dvd
    have h2 : ¬ (b + 1) ≤ (Nat.card (Outer X)).factorization 3 := fun hle =>
      hOut ((Nat.prime_three.pow_dvd_iff_le_factorization hn).mpr hle)
    omega
  have hcard : (Nat.card (MulAut X)).factorization 3 =
      (Nat.card Qbar * orderOf τ).factorization 3 := by
    have hleft : (Nat.card (MulAut X)).factorization 3 =
        b + (Nat.card (inner X)).factorization 3 := by
      have hmul := Nat.factorization_mul
        (Nat.card_pos (α := Outer X)).ne'
        (Nat.card_pos (α := ↥(inner X))).ne'
      have h3 := congrArg (fun f : ℕ →₀ ℕ => f 3) hmul
      simp only [Finsupp.add_apply] at h3
      rw [← hA, hOutFactor] at h3
      exact h3
    have hright : (Nat.card Qbar * orderOf τ).factorization 3 =
        b + (Nat.card (inner X)).factorization 3 := by
      have hmul := Nat.factorization_mul
        (Nat.card_pos (α := ↥Qbar)).ne'
        (by rw [horder]; positivity : orderOf τ ≠ 0)
      have h3 := congrArg (fun f : ℕ →₀ ℕ => f 3) hmul
      simp only [Finsupp.add_apply] at h3
      have hQbarfac : (Nat.card Qbar).factorization 3 = (Nat.card (inner X)).factorization 3 := by
        rw [hcardQbarSylow]
        exact Nat.factorization_pow_self Nat.prime_three
      have hτfac : (orderOf τ).factorization 3 = b := by
        rw [horder]
        exact Nat.factorization_pow_self Nat.prime_three
      rw [hQbarfac, hτfac] at h3
      rw [add_comm] at h3
      exact h3
    exact hleft.trans hright.symm
  obtain ⟨S, hS⟩ :=
    exists_sylow_omegaOne_le_center (inner X) Qbar hQbarSylow hQbarab τ s hs hτbar hτI hτp hcard
  exact omegaOne_le_center_of_sylow (inner X) S hS

theorem autOmegaCentral_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : AutOmegaCentral Y) : AutOmegaCentral X := by
  intro R hR
  let φ : MulAut X →* MulAut Y := (MulAut.congr e).toMonoidHom
  let R' : Subgroup (MulAut Y) := R.map φ
  have hR' : IsPGroup 3 R' := hR.map φ
  have hI : (inner X).map φ = inner Y :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
  have hinf : (R ⊓ inner X).map φ = R' ⊓ inner Y := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, ⟨hxR, hxI⟩, rfl⟩
      exact ⟨Subgroup.mem_map_of_mem φ hxR,
        by rw [← hI]; exact Subgroup.mem_map_of_mem φ hxI⟩
    · rintro y ⟨hyR, hyI⟩
      obtain ⟨x, hxR, rfl⟩ := hyR
      rw [← hI] at hyI
      obtain ⟨i, hiI, hi⟩ := hyI
      have hix : i = x := (MulAut.congr e).injective hi
      exact ⟨x, ⟨hxR, hix ▸ hiI⟩, rfl⟩
  have homega : (omegaOne 3 (R ⊓ inner X)).map φ = omegaOne 3 (R' ⊓ inner Y) := by
    rw [map_omegaOne φ (MulAut.congr e).injective.injOn 3, hinf]
  intro x hx
  have hxK : x ∈ R ⊓ inner X := omegaOne_le_self 3 (R ⊓ inner X) hx
  have hx' : φ x ∈ omegaOne 3 (R' ⊓ inner Y) := by
    rw [← homega]
    exact Subgroup.mem_map_of_mem φ hx
  have hhφx := h R' hR' hx'
  refine (mem_center_map_subtype_iff R).mpr ⟨hxK.1, fun r hr => ?_⟩
  have hcomm := (mem_center_map_subtype_iff R').mp hhφx
  have h2 := hcomm.2 (φ r) (Subgroup.mem_map_of_mem φ hr)
  apply (MulAut.congr e).injective
  simpa [φ, map_mul] using h2

theorem autOmegaCentral_of_oddInner {X : Type} [Group X] [Finite X]
    (hinner : ∀ α : MulAut X, IsPGroup 3 (Subgroup.zpowers α) → α ∈ inner X)
    (hab : ∀ Q : Sylow 3 X, ∀ x ∈ (Q : Subgroup X), ∀ y ∈ (Q : Subgroup X), x * y = y * x) :
    AutOmegaCentral X := by
  intro R hR
  have hRinner : R ≤ inner X := by
    intro a ha
    exact hinner a (hR.to_le (Subgroup.zpowers_le.mpr ha))
  have hRsub : IsPGroup 3 (R.subgroupOf (inner X)) := hR.comap_subtype
  obtain ⟨S', hRS'⟩ := hRsub.exists_le_sylow
  let f : X →* ↥(inner X) := (MulAut.conj : X →* MulAut X).rangeRestrict
  have hf : Function.Surjective f := MonoidHom.rangeRestrict_surjective _
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective (p := 3) hf S'
  have hS' : (S' : Subgroup ↥(inner X)) = (P : Subgroup X).map f := by
    rw [← hP, Sylow.coe_mapSurjective]
  have habelR : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    intro a ha b hb
    have ha' : (⟨a, hRinner ha⟩ : ↥(inner X)) ∈ (S' : Subgroup ↥(inner X)) :=
      hRS' (Subgroup.mem_subgroupOf.mpr ha)
    rw [hS'] at ha'
    obtain ⟨p, hpP, hpval⟩ := ha'
    have hb' : (⟨b, hRinner hb⟩ : ↥(inner X)) ∈ (S' : Subgroup ↥(inner X)) :=
      hRS' (Subgroup.mem_subgroupOf.mpr hb)
    rw [hS'] at hb'
    obtain ⟨q, hqP, hqval⟩ := hb'
    have haeq : a = MulAut.conj p := by
      have h1 : Subtype.val (f p) = a := congrArg Subtype.val hpval
      rw [← h1]
      exact MonoidHom.coe_rangeRestrict (MulAut.conj : X →* MulAut X) p
    have hbeq : b = MulAut.conj q := by
      have h1 : Subtype.val (f q) = b := congrArg Subtype.val hqval
      rw [← h1]
      exact MonoidHom.coe_rangeRestrict (MulAut.conj : X →* MulAut X) q
    rw [haeq, hbeq]
    calc MulAut.conj p * MulAut.conj q = MulAut.conj (p * q) :=
          (map_mul MulAut.conj p q).symm
      _ = MulAut.conj (q * p) := by rw [hab P p hpP q hqP]
      _ = MulAut.conj q * MulAut.conj p := map_mul MulAut.conj q p
  intro x hx
  have hxR : x ∈ R := (omegaOne_le_self 3 (R ⊓ inner X) hx).1
  refine (mem_center_map_subtype_iff R).mpr ⟨hxR, fun r hr => ?_⟩
  exact (habelR x hxR r hr).symm

theorem omegaOne_le_center_of_autOmegaCentral {G : Type} [Group G] [Finite G]
    {L P Q : Subgroup G} (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hP : IsPGroup 3 P)
    (hQL : Q ≤ L) (hQP : Q ≤ P)
    (hD : AutOmegaCentral (Bar2 L))
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 L))) :
    omegaOne 3 Q ≤ (Subgroup.center ↥P).map P.subtype := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxQ, hx3⟩
  have hxP : x ∈ P := hQP hxQ
  have hxL : x ∈ L := hQL hxQ
  let xq : ↥L := ⟨x, hxL⟩
  let ρ := CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L
  let R : Subgroup (MulAut (Bar2 L)) :=
    (P.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ
  have hR : IsPGroup 3 R := hP.comap_subtype.map ρ
  have key : ∀ y : ↥P, x * (y : G) = (y : G) * x := by
    intro y
    set yG : G := (y : G) with hyG
    have hyP : yG ∈ P := y.2
    have hyN : yG ∈ Subgroup.normalizer (L : Set G) := hPL hyP
    let m : ↥(Subgroup.normalizer (L : Set G)) := ⟨yG, hyN⟩
    let m' : ↥(Subgroup.normalizer (L : Set G)) := ⟨x, Subgroup.le_normalizer hxL⟩
    have hρx_eq : ρ m' = MulAut.conj (xq : Bar2 L) :=
      CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_inner L x hxL
    have hρx_R : ρ m' ∈ R := by
      refine Subgroup.mem_map_of_mem ρ ?_
      exact Subgroup.mem_subgroupOf.mpr hxP
    have hρy_R : ρ m ∈ R := by
      refine Subgroup.mem_map_of_mem ρ ?_
      exact Subgroup.mem_subgroupOf.mpr hyP
    have hρx3 : (ρ m') ^ 3 = 1 := by
      rw [← map_pow, show m' ^ 3 = 1 by ext; simpa using hx3, map_one]
    have hρx_omega : ρ m' ∈ omegaOne 3 (R ⊓ inner (Bar2 L)) :=
      Subgroup.subset_closure ⟨⟨hρx_R, by
        rw [hρx_eq]
        exact ⟨xq, rfl⟩⟩, hρx3⟩
    have hmem := hD R hR hρx_omega
    have hcomm_aut : ρ m * ρ m' = ρ m' * ρ m :=
      ((mem_center_map_subtype_iff R).mp hmem).2 (ρ m) hρy_R
    have hconj : ρ m * ρ m' * (ρ m)⁻¹ = ρ m' := by
      rw [hcomm_aut]
      group
    have hconj2 : MulAut.conj (ρ m (xq : Bar2 L)) = MulAut.conj (xq : Bar2 L) := by
      rw [(conj_conj (ρ m) (xq : Bar2 L)).symm, ← hρx_eq]
      exact hconj
    have hcenter : ρ m (xq : Bar2 L) * (xq : Bar2 L)⁻¹ ∈ Subgroup.center (Bar2 L) :=
      conj_eq_conj_iff.mp hconj2
    have hyxyl : yG * x * yG⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hyN x).mp hxL
    have hu : ρ m (xq : Bar2 L) = QuotientGroup.mk (⟨yG * x * yG⁻¹, hyxyl⟩ : ↥L) := by
      rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk L m xq]
      exact congrArg QuotientGroup.mk (Subtype.ext
        (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk_coe L m xq))
    let w : G := yG * x * yG⁻¹ * x⁻¹
    have hwL : w ∈ L := mul_mem hyxyl (inv_mem hxL)
    have hwP : w ∈ P := mul_mem (mul_mem (mul_mem hyP hxP) (inv_mem hyP)) (inv_mem hxP)
    let W : Bar2 L := QuotientGroup.mk (⟨w, hwL⟩ : ↥L)
    have hw_hcenter : W ∈ Subgroup.center (Bar2 L) := by
      have hw_eq : ρ m (xq : Bar2 L) * (xq : Bar2 L)⁻¹ = W := by
        rw [hu, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        congr 1
      rwa [← hw_eq]
    obtain ⟨k, hk⟩ := hP ⟨w, hwP⟩
    have hw3 : w ^ 3 ^ k = 1 := by
      have := congrArg (fun z : ↥P => (z : G)) hk
      simpa using this
    have hzpow3 : W ^ (3 ^ k) = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨w, hwL⟩ : ↥L) ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hw3)
      rw [this, QuotientGroup.mk_one]
    have hz_dvd : orderOf W ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one hzpow3
    have hz_card : orderOf W ∣ Nat.card (Subgroup.center (Bar2 L)) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center (Bar2 L)) hw_hcenter
    have hz1 : W = 1 := by
      by_contra hne
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hz_dvd
      have hjne : j ≠ 0 := by
        intro h0
        exact hne (orderOf_eq_one_iff.mp (by rw [hj, h0, pow_zero]))
      have h3 : 3 ∣ orderOf W := by
        rw [hj]
        exact dvd_pow_self 3 hjne
      exact hZ (h3.trans hz_card)
    have hwcore : (⟨w, hwL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
      (QuotientGroup.eq_one_iff _).mp hz1
    obtain ⟨m2, hm2⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨⟨w, hwL⟩, hwcore⟩
    have hm2' : (⟨w, hwL⟩ : ↥L) ^ 2 ^ m2 = 1 := by
      have := congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => (z : ↥L)) hm2
      simpa using this
    have hd1 : orderOf (⟨w, hwL⟩ : ↥L) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hw3))
    have hd2 : orderOf (⟨w, hwL⟩ : ↥L) ∣ 2 ^ m2 :=
      orderOf_dvd_of_pow_eq_one hm2'
    have hcop : Nat.Coprime (3 ^ k) (2 ^ m2) :=
      Nat.Coprime.pow k m2 (by norm_num : Nat.Coprime 3 2)
    have hone : orderOf (⟨w, hwL⟩ : ↥L) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    have hw1 : (⟨w, hwL⟩ : ↥L) = 1 := orderOf_eq_one_iff.mp hone
    have hwG : w = 1 := congrArg Subtype.val hw1
    have hwx : yG * x * yG⁻¹ = x := by
      have := congrArg (fun t : G => t * x) (show yG * x * yG⁻¹ * x⁻¹ = 1 from hwG)
      simpa [mul_assoc] using this
    have hyx : yG * x = x * yG := by
      have := congrArg (fun t : G => t * yG) hwx
      simpa [mul_assoc] using this
    exact hyx.symm
  refine ⟨⟨x, hxP⟩, Subgroup.mem_center_iff.mpr (fun y => Subtype.ext ?_), rfl⟩
  exact (key y).symm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
