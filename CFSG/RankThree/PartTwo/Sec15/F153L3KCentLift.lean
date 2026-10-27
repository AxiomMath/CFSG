module

public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K

open CFSG CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14

theorem eq_one_of_pow_two_of_odd_card {Z : Type} [Group Z] [Finite Z] (hZ : Odd (Nat.card Z))
    {z : Z} (h : z ^ 2 = 1) : z = 1 := by
  have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one h
  have hn : orderOf z ∣ Nat.card Z := orderOf_dvd_natCard z
  rw [← orderOf_eq_one_iff]
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
  · exact h1
  · exfalso
    rw [h1] at hn
    obtain ⟨k, hk⟩ := hZ
    omega

theorem orderOf_quot_center_of_involution {Q : Type} [Group Q] [Finite Q]
    (hZ : Odd (Nat.card (Subgroup.center Q))) {x : Q} (hx : orderOf x = 2) :
    orderOf (x : Q ⧸ Subgroup.center Q) = 2 := by
  have hx2 : x ^ 2 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx] at h
  have hsq : (x : Q ⧸ Subgroup.center Q) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hx2, QuotientGroup.mk_one]
  have hne : (x : Q ⧸ Subgroup.center Q) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    have hdvd : orderOf (⟨x, h1⟩ : Subgroup.center Q) ∣ Nat.card (Subgroup.center Q) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hx] at hdvd
    obtain ⟨k, hk⟩ := hZ
    omega
  exact orderOf_eq_prime hsq hne

theorem eq_of_involution_lift {Q : Type} [Group Q] [Finite Q]
    (hZ : Odd (Nat.card (Subgroup.center Q))) {x y : Q} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (h : (x : Q ⧸ Subgroup.center Q) = (y : Q ⧸ Subgroup.center Q)) : x = y := by
  have hx2 : x ^ 2 = 1 := by
    have h' := pow_orderOf_eq_one x
    rwa [hx] at h'
  have hy2 : y ^ 2 = 1 := by
    have h' := pow_orderOf_eq_one y
    rwa [hy] at h'
  have hz : x⁻¹ * y ∈ Subgroup.center Q := QuotientGroup.eq.mp h
  have hxy : x * (x⁻¹ * y) = y := mul_inv_cancel_left x y
  have hc : Commute x (x⁻¹ * y) := Subgroup.mem_center_iff.mp hz x
  have hkey : (x * (x⁻¹ * y)) ^ 2 = 1 := by
    rw [hxy]
    exact hy2
  rw [hc.mul_pow, hx2, one_mul] at hkey
  have hz1 : (⟨x⁻¹ * y, hz⟩ : Subgroup.center Q) = 1 := by
    apply eq_one_of_pow_two_of_odd_card hZ
    apply Subtype.ext
    simpa using hkey
  have hz1' : x⁻¹ * y = 1 := congrArg Subtype.val hz1
  calc x = x * (x⁻¹ * y) := by rw [hz1', mul_one]
    _ = y := hxy

theorem exists_involution_lift {Q : Type} [Group Q] [Finite Q]
    (hZ : Odd (Nat.card (Subgroup.center Q))) (xb : Q ⧸ Subgroup.center Q) (hx : orderOf xb = 2) :
    ∃ x : Q, orderOf x = 2 ∧ (x : Q ⧸ Subgroup.center Q) = xb := by
  obtain ⟨x0, rfl⟩ := QuotientGroup.mk_surjective xb
  have hxb2 : (x0 : Q ⧸ Subgroup.center Q) ^ 2 = 1 := by
    have h' := pow_orderOf_eq_one (x0 : Q ⧸ Subgroup.center Q)
    rwa [hx] at h'
  have hcen : x0 ^ 2 ∈ Subgroup.center Q := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hxb2
  have hpow : (x0 : Q ⧸ Subgroup.center Q) ^ Nat.card (Subgroup.center Q)
      = (x0 : Q ⧸ Subgroup.center Q) := by
    obtain ⟨k, hk⟩ := hZ
    rw [hk, pow_succ, pow_mul, hxb2, one_pow, one_mul]
  have hsq0 : (x0 ^ 2) ^ Nat.card (Subgroup.center Q) = 1 := by
    have hw : (⟨x0 ^ 2, hcen⟩ : Subgroup.center Q) ^ Nat.card (Subgroup.center Q) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard _)
    have hw' := congrArg Subtype.val hw
    rw [Subgroup.coe_pow] at hw'
    exact hw'
  refine ⟨x0 ^ Nat.card (Subgroup.center Q), ?_, ?_⟩
  · have hsq : (x0 ^ Nat.card (Subgroup.center Q)) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      exact hsq0
    have hne : x0 ^ Nat.card (Subgroup.center Q) ≠ 1 := by
      intro h1
      have h2 : (x0 : Q ⧸ Subgroup.center Q) ^ Nat.card (Subgroup.center Q) = 1 := by
        rw [← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
      rw [hpow] at h2
      rw [h2, orderOf_one] at hx
      omega
    exact orderOf_eq_prime hsq hne
  · rw [QuotientGroup.mk_pow]
    exact hpow

@[expose] def S3PartnerFixed (T : Type) [Group T] : Prop :=
  ∀ t : T, orderOf t = 2 → ∀ D : Subgroup (MulAut T), IsPGroup 3 D → (∀ d ∈ D, d t = t) →
    ∃ x : T, orderOf x = 2 ∧ (∀ d ∈ D, d x = x) ∧ orderOf (t * x) = 3

private theorem prop_preserved {T : Type} [Group T] {t : T} {d : MulAut T} (hd : d t = t) (x : T)
    (hx : orderOf x = 2 ∧ orderOf (t * x) = 3) :
    orderOf (d x) = 2 ∧ orderOf (t * d x) = 3 := by
  have e : ∀ y : T, orderOf (d y) = orderOf y := fun y => MulEquiv.orderOf_eq d y
  have h1 : t * d x = d (t * x) := by
    rw [map_mul, hd]
  refine ⟨?_, ?_⟩
  · rw [e]
    exact hx.1
  · rw [h1, e]
    exact hx.2

@[instance_reducible] private def actE {T : Type} [Group T] (t : T) (D : Subgroup (MulAut T))
    (hD : ∀ d ∈ D, d t = t) :
    MulAction D {x : T // orderOf x = 2 ∧ orderOf (t * x) = 3} where
  smul g x := ⟨(g : MulAut T) x.1, prop_preserved (hD (g : MulAut T) g.2) x.1 x.2⟩
  one_smul x := Subtype.ext rfl
  mul_smul g h x := Subtype.ext rfl

theorem s3PartnerFixed_of_card {T : Type} [Group T]
    (h : ∀ t : T, orderOf t = 2 →
      ¬ 3 ∣ Nat.card {x : T // orderOf x = 2 ∧ orderOf (t * x) = 3}) : S3PartnerFixed T := by
  intro t ht D hD hfix
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI act : MulAction D {x : T // orderOf x = 2 ∧ orderOf (t * x) = 3} := actE t D hfix
  obtain ⟨⟨x, hx⟩, hmem⟩ :=
    IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hD
      {x : T // orderOf x = 2 ∧ orderOf (t * x) = 3} (h t ht)
  refine ⟨x, hx.1, fun d hd => ?_, hx.2⟩
  have hd' := MulAction.mem_fixedPoints.mp hmem ⟨d, hd⟩
  exact congrArg Subtype.val hd'

@[expose] noncomputable def descent (Q : Type) [Group Q] :
    MulAut Q →* MulAut (Q ⧸ Subgroup.center Q) where
  toFun σ := QuotientGroup.congr _ _ σ (Subgroup.map_center_eq σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem descent_mk {Q : Type} [Group Q] (σ : MulAut Q) (q : Q) :
    descent Q σ (q : Q ⧸ Subgroup.center Q) = ((σ q : Q) : Q ⧸ Subgroup.center Q) := rfl

theorem coprime_orderOf_of_mem_pPrimeCoreOf {Q : Type} [Group Q] [Finite Q] (K : Subgroup Q)
    {g : Q} (hg : g ∈ pPrimeCoreOf 3 K) : Nat.Coprime 3 (orderOf g) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.1 hg
  have h1 : orderOf (K.subtype g') = orderOf g' :=
    orderOf_injective K.subtype K.subtype_injective g'
  have h2 : orderOf (⟨g', hg'⟩ : ↥(pPrimeCore 3 ↥K)) ∣ Nat.card (pPrimeCore 3 ↥K) :=
    orderOf_dvd_natCard _
  have h3 : orderOf (⟨g', hg'⟩ : ↥(pPrimeCore 3 ↥K)) = orderOf g' := Subgroup.orderOf_mk g' hg'
  rw [h1]
  exact Nat.Coprime.coprime_dvd_right (h3 ▸ h2) CFSG.pPrimeCore_coprime_card

theorem conj_mem_pPrimeCoreOf {Q : Type} [Group Q] (K : Subgroup Q) {c t : Q} (hc : c ∈ K)
    (ht : t ∈ pPrimeCoreOf 3 K) : c * t * c⁻¹ ∈ pPrimeCoreOf 3 K := by
  obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
  refine Subgroup.mem_map.2 ⟨(⟨c, hc⟩ : ↥K) * t' * (⟨c, hc⟩ : ↥K)⁻¹, ?_, ?_⟩
  · exact (CFSG.pPrimeCore_normal (p := 3) (G := ↥K)).conj_mem t' ht' ⟨c, hc⟩
  · simp

theorem odd_card_pPrimeCoreOf_of_s3PartnerFixed {Q : Type} [Group Q] [Finite Q]
    (hZ : Odd (Nat.card (Subgroup.center Q))) (hS : S3PartnerFixed (Q ⧸ Subgroup.center Q))
    (D : Subgroup (MulAut Q)) (hD : IsPGroup 3 D) :
    Odd (Nat.card ↥(pPrimeCoreOf 3 (FixedPoints.subgroup D Q))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup Q := FixedPoints.subgroup D Q with hC
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(pPrimeCoreOf 3 C) := by
    rcases Nat.even_or_odd (Nat.card ↥(pPrimeCoreOf 3 C)) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hodd
  obtain ⟨tN, htN⟩ := exists_prime_orderOf_dvd_card' (G := ↥(pPrimeCoreOf 3 C)) 2 h2
  set t : Q := (tN : Q) with ht
  have htmem : t ∈ pPrimeCoreOf 3 C := tN.2
  have ht2 : orderOf t = 2 := by
    have : orderOf (tN : Q) = orderOf tN := Subgroup.orderOf_coe tN
    rw [ht, this, htN]
  have htC : t ∈ C := Subgroup.map_subtype_le (pPrimeCore 3 ↥C) htmem
  have hfix : ∀ y ∈ C, ∀ d ∈ D, d y = y := by
    intro y hy d hd
    exact (show ∀ m : ↥D, m • y = y from hy) ⟨d, hd⟩
  have htfix : ∀ d ∈ D, d t = t := hfix t htC
  set Z := Subgroup.center Q with hZdef
  have htb : orderOf (t : Q ⧸ Z) = 2 := orderOf_quot_center_of_involution hZ ht2
  set Db : Subgroup (MulAut (Q ⧸ Z)) := D.map (descent Q) with hDb
  have hDbp : IsPGroup 3 Db :=
    IsPGroup.of_surjective hD ((descent Q).subgroupMap D) (MonoidHom.subgroupMap_surjective _ _)
  have htbfix : ∀ e ∈ Db, e (t : Q ⧸ Z) = (t : Q ⧸ Z) := by
    rintro e ⟨d, hd, rfl⟩
    rw [descent_mk, htfix d hd]
  obtain ⟨xb, hxb2, hxbfix, hxt3⟩ := hS (t : Q ⧸ Z) htb Db hDbp htbfix
  obtain ⟨x, hx2, hxmk⟩ := exists_involution_lift hZ xb hxb2
  have hxC : x ∈ C := by
    show ∀ m : ↥D, m • x = x
    rintro ⟨d, hd⟩
    show d x = x
    refine eq_of_involution_lift hZ ?_ hx2 ?_
    · rw [MulEquiv.orderOf_eq]; exact hx2
    · have h1 : descent Q d xb = xb := hxbfix _ ⟨d, hd, rfl⟩
      rw [← descent_mk, hxmk, h1]
  have hg : t * (x * t * x⁻¹) ∈ pPrimeCoreOf 3 C :=
    Subgroup.mul_mem _ htmem (conj_mem_pPrimeCoreOf C hxC htmem)
  have hcop := coprime_orderOf_of_mem_pPrimeCoreOf C hg
  have hxinv : xb⁻¹ = xb := by
    have : xb * xb = 1 := by rw [← pow_two, ← hxb2]; exact pow_orderOf_eq_one xb
    exact inv_eq_of_mul_eq_one_right this
  have himg : ((t * (x * t * x⁻¹) : Q) : Q ⧸ Z) = ((t : Q ⧸ Z) * xb) ^ 2 := by
    have e1 : ((x⁻¹ : Q) : Q ⧸ Z) = xb := by rw [QuotientGroup.mk_inv, hxmk, hxinv]
    have e2 : ((t * (x * t * x⁻¹) : Q) : Q ⧸ Z) = (t : Q ⧸ Z) * (xb * (t : Q ⧸ Z) * xb) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, e1, hxmk]
    rw [e2, pow_two]
    group
  have h3 : orderOf (((t : Q ⧸ Z) * xb) ^ 2) = 3 := by
    rw [Nat.Coprime.orderOf_pow (by rw [hxt3]; norm_num), hxt3]
  have hdvd : 3 ∣ orderOf (t * (x * t * x⁻¹)) := by
    have := orderOf_map_dvd (QuotientGroup.mk' Z) (t * (x * t * x⁻¹))
    rw [QuotientGroup.mk'_apply, himg, h3] at this
    exact this
  have := Nat.Coprime.eq_one_of_dvd hcop hdvd
  omega

theorem kFactL3CentOdd_of_s3PartnerFixed
    (h : ∀ (T : Type) [Group T] [Finite T] (f : ℕ), 1 ≤ f →
      (letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; IsLThreeEpsAt T 2 f) → S3PartnerFixed T) :
    F153L3C2.KFactL3CentOdd := by
  intro Q _ _ f hf _ hZ hT D hD
  have hDp : IsPGroup 3 D := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hD.2 g g.2⟩
  exact odd_card_pPrimeCoreOf_of_s3PartnerFixed hZ (h _ f hf hT) D hDp

end CFSG.RankThree.PartTwo.Sec15.F153L3K
