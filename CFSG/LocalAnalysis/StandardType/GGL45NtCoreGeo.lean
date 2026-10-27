module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
import CFSG.LocalAnalysis.StandardType.GGL45NtGroupLemmas

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL45NtCoreHyp (p : ℕ) {R : Type} [Group R] (I F : Set (MulAut R))
    (Ebar : Subgroup (MulAut R)) (f' : MulAut R) : Prop :=
  IsElemAbelian p Ebar ∧ p ^ 2 ≤ Nat.card Ebar ∧ (∀ e ∈ Ebar, e ∈ I) ∧ f' ^ p = 1 ∧
    (∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧ f' = u * f * u⁻¹) ∧ (∀ e ∈ Ebar, e * f' = f' * e) ∧
    (∀ r : R, r ^ p = 1 → (∀ e ∈ Ebar, e r = r) → f' r = r → MulAut.conj r ∈ Ebar)

@[expose] def GGL45NtGeo (p : ℕ) {R : Type} [Group R] (I : Set (MulAut R))
    (Ebar : Subgroup (MulAut R)) (f' : MulAut R) : Prop :=
  (∀ u v : MulAut R, GGL45NtCIp p I Ebar u → GGL45NtCIp p I Ebar v → u * v = v * u) ∧
  (∀ u : MulAut R, GGL45NtCIp p I Ebar u → ∀ w ∈ I, (∀ e ∈ Ebar, w * e = e * w) → w * u = u * w) ∧
  ∃ N : ℕ, 2 ≤ N ∧ (∀ u : MulAut R, GGL45NtCIp p I Ebar u → f' * u * f'⁻¹ = u ^ N) ∧
    ∀ a : MulAut R, GGL45NtCIp p I Ebar a → f' * a * f'⁻¹ = a →
      ∃ b : MulAut R, GGL45NtCIp p I Ebar b ∧ a = b ^ (∑ i ∈ Finset.range p, N ^ i)

@[expose] def GGL45NtGeoRaw (p : ℕ) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ (Ebar : Subgroup (MulAut R)) (f' : MulAut R), GGL45NtCoreHyp p I F Ebar f' →
      GGL45NtGeo p I Ebar f'

@[expose] def GGL45NtGeoOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  GGL45NtOn S fun p _ => GGL45NtGeoRaw p

@[expose] def GGL45NtStruct : LargeEvenRawCont :=
  fun R _ I _ => Finite R ∧ (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∃ J : Subgroup (MulAut R), (J : Set (MulAut R)) = I)

@[expose] def GGL45NtStructOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  GGL45NtOn S fun _ _ => GGL45NtStruct

theorem ggL45NtCore_of_geo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R] [Finite R]
    {I F : Set (MulAut R)} (hI : ∃ J : Subgroup (MulAut R), (J : Set (MulAut R)) = I)
    (hgeo : ∀ (Ebar : Subgroup (MulAut R)) (f' : MulAut R), GGL45NtCoreHyp p I F Ebar f' →
      GGL45NtGeo p I Ebar f') :
    ∀ (Ebar : Subgroup (MulAut R)) (f' : MulAut R),
      IsElemAbelian p Ebar → p ^ 2 ≤ Nat.card Ebar → (∀ e ∈ Ebar, e ∈ I) →
      f' ^ p = 1 → (∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧ f' = u * f * u⁻¹) →
      (∀ e ∈ Ebar, e * f' = f' * e) →
      (∀ r : R, r ^ p = 1 → (∀ e ∈ Ebar, e r = r) → f' r = r → MulAut.conj r ∈ Ebar) →
      ∃ s : ℕ, 2 ≤ s ∧ ∃ (c : ℤ) (k : ℕ), ¬ p ∣ k ∧
        c ≡ 1 + (p : ℤ) ^ (s - 1) * k [ZMOD (p : ℤ) ^ s] ∧
        (∀ u v : MulAut R, GGL45NtCIp p I Ebar u → GGL45NtCIp p I Ebar v → u * v = v * u) ∧
        (∀ u : MulAut R, GGL45NtCIp p I Ebar u → u ^ p ^ s = 1 ∧ f' * u * f'⁻¹ = u ^ c) ∧
        (∀ u : MulAut R, GGL45NtCIp p I Ebar u → ∀ w ∈ I, (∀ e ∈ Ebar, w * e = e * w) →
          w * u = u * w) ∧
        ∃ a₁ a₂ : MulAut R, GGL45NtCIp p I Ebar a₁ ∧ GGL45NtCIp p I Ebar a₂ ∧
          ∀ i j : ℕ, (a₁ ^ p ^ (s - 1)) ^ i * (a₂ ^ p ^ (s - 1)) ^ j = 1 → p ∣ i ∧ p ∣ j := by
  intro Ebar f' hEab hEcard hEsub hf'p hf'conj hcomm hsat
  obtain ⟨J, hJ⟩ := hI
  have hIJ : ∀ {u : MulAut R}, u ∈ J ↔ u ∈ I := by
    intro u
    exact Set.ext_iff.mp hJ u
  have hcore : GGL45NtCoreHyp p I F Ebar f' :=
    ⟨hEab, hEcard, hEsub, hf'p, hf'conj, hcomm, hsat⟩
  obtain ⟨hgeo1, hgeo2central, N, hN2, hNpow, hNnorm⟩ := hgeo Ebar f' hcore
  have hEsubA : ∀ e ∈ Ebar, GGL45NtCIp p I Ebar e := by
    intro e he
    refine ⟨hEsub e he, ?_, ⟨1, ?_⟩⟩
    · intro f hf
      simpa using hEab.1.is_comm.comm (⟨e, he⟩ : Ebar) (⟨f, hf⟩ : Ebar)
    · simpa using hEab.2 e he
  let Asub : Subgroup (MulAut R) :=
    { carrier := {u | GGL45NtCIp p I Ebar u}
      one_mem' := by
        refine ⟨hIJ.mp J.one_mem, ?_, ⟨0, by simp⟩⟩
        intro e _
        rw [one_mul, mul_one]
      mul_mem' := by
        rintro u v hu hv
        have hu' : GGL45NtCIp p I Ebar u := hu
        have hv' : GGL45NtCIp p I Ebar v := hv
        obtain ⟨huI, huE, huP⟩ := hu
        obtain ⟨hvI, hvE, hvP⟩ := hv
        refine ⟨hIJ.mp (J.mul_mem (hIJ.mpr huI) (hIJ.mpr hvI)), ?_, ?_⟩
        · intro e he
          calc (u * v) * e = u * (v * e) := by rw [mul_assoc]
            _ = u * (e * v) := by rw [hvE e he]
            _ = (u * e) * v := by rw [mul_assoc]
            _ = (e * u) * v := by rw [huE e he]
            _ = e * (u * v) := by rw [mul_assoc]
        · obtain ⟨a, ha⟩ := huP
          obtain ⟨b, hb⟩ := hvP
          have huv : Commute u v := hgeo1 u v hu' hv'
          have hua : u ^ p ^ (a + b) = 1 := by
            rw [pow_add, pow_mul, ha, one_pow]
          have hvb : v ^ p ^ (a + b) = 1 := by
            rw [pow_add, mul_comm (p ^ a) (p ^ b), pow_mul, hb, one_pow]
          exact ⟨a + b, by rw [huv.mul_pow (p ^ (a + b)), hua, hvb, mul_one]⟩
      inv_mem' := by
        rintro u ⟨huI, huE, huP⟩
        refine ⟨hIJ.mp (J.inv_mem (hIJ.mpr huI)), ?_, ?_⟩
        · intro e he
          exact (show Commute u e from huE e he).inv_left.eq
        · obtain ⟨a, ha⟩ := huP
          exact ⟨a, by rw [inv_pow, ha, inv_one]⟩ }
  have hAmem : ∀ u : MulAut R, u ∈ Asub ↔ GGL45NtCIp p I Ebar u := fun _ => Iff.rfl
  letI cA : CommGroup Asub :=
    { (inferInstance : Group Asub) with
      mul_comm := fun x y => Subtype.ext (by
        simpa using hgeo1 x.1 y.1 ((hAmem x.1).mp x.2) ((hAmem y.1).mp y.2)) }
  have hApg : @IsPGroup p Asub cA.toGroup := by
    intro g
    obtain ⟨k, hk⟩ := ((hAmem g.1).mp g.2).2.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hconj : ∀ (x : MulAut R) (n : ℕ), f' * x ^ n * f'⁻¹ = (f' * x * f'⁻¹) ^ n :=
    fun x n => (conj_pow (a := f') (b := x) (i := n)).symm
  have hF : ∀ a : Asub, a ^ N ^ p = a := by
    intro a
    have key : ∀ i : ℕ, (f' ^ i) * (a : MulAut R) * (f' ^ i)⁻¹ = (a : MulAut R) ^ N ^ i := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have step : (f' ^ (i + 1)) * (a : MulAut R) * (f' ^ (i + 1))⁻¹
            = f' * ((f' ^ i) * (a : MulAut R) * (f' ^ i)⁻¹) * f'⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          group
        rw [step, ih, hconj (a : MulAut R) (N ^ i),
          hNpow (a : MulAut R) ((hAmem (a : MulAut R)).mp a.2), ← pow_mul, pow_succ']
    have hp' := key p
    rw [hf'p, one_mul, inv_one, mul_one] at hp'
    exact Subtype.ext (by simpa using hp'.symm)
  have hnorm : ∀ a : Asub, a ^ N = a → ∃ b : Asub, a = ∏ i ∈ Finset.range p, b ^ N ^ i := by
    intro a ha
    have ha' : f' * (a : MulAut R) * f'⁻¹ = (a : MulAut R) := by
      rw [hNpow (a : MulAut R) ((hAmem (a : MulAut R)).mp a.2)]
      exact congrArg Subtype.val ha
    obtain ⟨b, hbC, hb⟩ := hNnorm (a : MulAut R) ((hAmem (a : MulAut R)).mp a.2) ha'
    refine ⟨⟨b, hbC⟩, ?_⟩
    rw [Finset.prod_pow_eq_pow_sum (Finset.range p) (fun i => N ^ i) (⟨b, hbC⟩ : Asub)]
    exact Subtype.ext hb
  have hN1 : N ≠ 1 := by omega
  have hN : N ≡ 1 [MOD p] := by
    haveI : Fintype Ebar := Fintype.ofFinite Ebar
    have hEcardF : p ^ 2 ≤ Fintype.card Ebar := by
      rw [← Nat.card_eq_fintype_card]; exact hEcard
    have h1lt : 1 < Fintype.card Ebar := by
      have : 1 < p ^ 2 := by nlinarith [hp.two_le]
      omega
    obtain ⟨e₁, he₁ne⟩ := Fintype.exists_ne_of_one_lt_card h1lt (1 : Ebar)
    haveI : Fact p.Prime := ⟨hp⟩
    have horder₁ : orderOf (e₁ : MulAut R) = p :=
      orderOf_eq_prime (hEab.2 (e₁ : MulAut R) e₁.2) (by
        intro h
        exact he₁ne (Subtype.ext (by simpa using h)))
    have hfix : (e₁ : MulAut R) ^ N = (e₁ : MulAut R) := by
      have h1 : f' * (e₁ : MulAut R) * f'⁻¹ = (e₁ : MulAut R) := by
        rw [← hcomm (e₁ : MulAut R) e₁.2]
        group
      rw [← hNpow (e₁ : MulAut R) (hEsubA (e₁ : MulAut R) e₁.2)]
      exact h1
    have hdvd : p ∣ N - 1 := by
      have hpow : (e₁ : MulAut R) ^ (N - 1) = 1 := by
        have h := hfix
        rw [show N = (N - 1) + 1 by omega, pow_succ] at h
        exact mul_right_cancel h
      have := orderOf_dvd_iff_pow_eq_one.mpr hpow
      rwa [horder₁] at this
    exact ((Nat.modEq_iff_dvd' (by omega : 1 ≤ N)).mpr hdvd).symm
  obtain ⟨s, hs2, hkex, hexp, homega⟩ :=
    CFSG.HardMathSupport.C14Group.homocyclic_of_norm_surjective (A := Asub) hp hp2 hApg hN hN1 hF hnorm
  obtain ⟨k, hk, hNmod⟩ := hkex
  refine ⟨s, hs2, (N : ℤ), k, hk, ?_, hgeo1, ?_, hgeo2central, ?_⟩
  · have h := (Int.natCast_modEq_iff).mpr hNmod
    simpa using h
  · intro u hu
    constructor
    · have := hexp ⟨u, (hAmem u).mpr hu⟩
      simpa using congrArg Subtype.val this
    · rw [zpow_natCast]
      exact hNpow u hu
  · have hEA : ∀ e ∈ Ebar, e ∈ Asub := fun e he => (hAmem e).mpr (hEsubA e he)
    haveI : Fintype Ebar := Fintype.ofFinite Ebar
    have hEcardF : p ^ 2 ≤ Fintype.card Ebar := by
      rw [← Nat.card_eq_fintype_card]; exact hEcard
    have h1lt : 1 < Fintype.card Ebar := by
      have : 1 < p ^ 2 := by nlinarith [hp.two_le]
      omega
    obtain ⟨e₁, he₁ne⟩ := Fintype.exists_ne_of_one_lt_card h1lt (1 : Ebar)
    haveI : Fact p.Prime := ⟨hp⟩
    have horder₁ : orderOf (e₁ : MulAut R) = p :=
      orderOf_eq_prime (hEab.2 (e₁ : MulAut R) e₁.2) (by
        intro h
        exact he₁ne (Subtype.ext (by simpa using h)))
    have hcard_zp : Nat.card (Subgroup.zpowers (e₁ : MulAut R)) = p := by
      rw [Nat.card_zpowers, horder₁]
    have hzp_le : Subgroup.zpowers (e₁ : MulAut R) ≤ Ebar :=
      Subgroup.zpowers_le.mpr e₁.2
    have hproper : Nat.card (Subgroup.zpowers (e₁ : MulAut R)) < Nat.card Ebar := by
      rw [hcard_zp]
      have : p < p ^ 2 := by nlinarith [hp.two_le]
      linarith [hEcard]
    have he₂ : ∃ e₂ : MulAut R, e₂ ∈ Ebar ∧ e₂ ∉ Subgroup.zpowers (e₁ : MulAut R) := by
      by_contra h
      push_neg at h
      have hle : Ebar ≤ Subgroup.zpowers (e₁ : MulAut R) := fun x hx => h x hx
      have heq : Ebar = Subgroup.zpowers (e₁ : MulAut R) := le_antisymm hle hzp_le
      have hcard_eq : Nat.card Ebar = Nat.card (Subgroup.zpowers (e₁ : MulAut R)) :=
        congrArg (fun H : Subgroup (MulAut R) => Nat.card H) heq
      rw [hcard_eq] at hproper
      exact absurd hproper (lt_irrefl _)
    obtain ⟨e₂, he₂mem, he₂not⟩ := he₂
    have he₂ne : e₂ ≠ 1 := by
      intro h
      exact he₂not (by rw [h]; exact Subgroup.one_mem _)
    have horder₂ : orderOf e₂ = p :=
      orderOf_eq_prime (hEab.2 e₂ he₂mem) he₂ne
    have hindep : ∀ i j : ℕ, (e₁ : MulAut R) ^ i * e₂ ^ j = 1 → p ∣ i ∧ p ∣ j := by
      intro i j hij
      have hmem₁ : e₂ ^ j ∈ Subgroup.zpowers (e₁ : MulAut R) := by
        have h : e₂ ^ j = ((e₁ : MulAut R) ^ i)⁻¹ := (mul_eq_one_iff_eq_inv').mp hij
        rw [h]
        exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ i)
      have hpj : p ∣ j := by
        by_contra hnot
        have hcop : Nat.Coprime j (orderOf e₂) := by
          rw [horder₂]
          exact (hp.coprime_iff_not_dvd.mpr hnot).symm
        have hmem₂ : e₂ ∈ Subgroup.zpowers (e₂ ^ j) := mem_zpowers_pow_iff.mpr hcop
        have hle : Subgroup.zpowers (e₂ ^ j) ≤ Subgroup.zpowers (e₁ : MulAut R) :=
          Subgroup.zpowers_le.mpr hmem₁
        exact he₂not (hle hmem₂)
      refine ⟨?_, hpj⟩
      have h₁ : (e₁ : MulAut R) ^ i = 1 := by
        obtain ⟨m, rfl⟩ := hpj
        rw [pow_mul, hEab.2 e₂ he₂mem, one_pow, mul_one] at hij
        exact hij
      have hdiv : orderOf (e₁ : MulAut R) ∣ i := orderOf_dvd_iff_pow_eq_one.mpr h₁
      rwa [horder₁] at hdiv
    have he₁p : (⟨(e₁ : MulAut R), hEA _ e₁.2⟩ : Asub) ^ p = 1 :=
      Subtype.ext (by simpa using hEab.2 (e₁ : MulAut R) e₁.2)
    have he₂p : (⟨e₂, hEA _ he₂mem⟩ : Asub) ^ p = 1 :=
      Subtype.ext (by simpa using hEab.2 e₂ he₂mem)
    obtain ⟨A₁, hA₁⟩ := homega ⟨(e₁ : MulAut R), hEA _ e₁.2⟩ he₁p
    obtain ⟨A₂, hA₂⟩ := homega ⟨e₂, hEA _ he₂mem⟩ he₂p
    refine ⟨(A₁ : MulAut R), (A₂ : MulAut R), (hAmem _).mp A₁.2, (hAmem _).mp A₂.2, ?_⟩
    intro i j h
    apply hindep i j
    have hA₁' : (e₁ : MulAut R) = (A₁ : MulAut R) ^ p ^ (s - 1) := by
      have := congrArg Subtype.val hA₁
      simpa using this
    have hA₂' : e₂ = (A₂ : MulAut R) ^ p ^ (s - 1) := by
      have := congrArg Subtype.val hA₂
      simpa using this
    rw [← hA₁', ← hA₂'] at h
    exact h

end CFSG.StandardType
