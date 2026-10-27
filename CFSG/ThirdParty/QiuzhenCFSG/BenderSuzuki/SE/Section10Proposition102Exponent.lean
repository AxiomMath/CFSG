module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Core
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Support

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Proposition 10.2(c): inverted-set arithmetic

This module proves the generic group-theoretic and arithmetic endpoints used
to derive the formula `m = r^a (2^p - 1)`.  The source-specific Sylow-factor
assembly is kept separate from these reusable facts.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- A normalizer of a subgroup normalizes the ambient image of each
characteristic subgroup. -/
public theorem proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
    {X : Type u} [Group X] (H : Subgroup X) (K : Subgroup H)
    [K.Characteristic] :
    Subgroup.normalizer (H : Set X) ≤
      Subgroup.normalizer (K.map H.subtype : Set X) := by
  classical
  refine subgroup_le_normalizer_of_conj_mem (K.map H.subtype)
    (Subgroup.normalizer (H : Set X)) ?_
  intro g x hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, hxK, rfl⟩
  let gH : Subgroup.normalizer (H : Set X) := ⟨g, g.property⟩
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K = K :=
    (inferInstance : K.Characteristic).fixed (Subgroup.normalizerMonoidHom H gH)
  have hxComap :
      xH ∈ Subgroup.comap
        (Subgroup.normalizerMonoidHom H gH).toMonoidHom K := by
    rw [hfix]
    exact hxK
  have hxImage : (Subgroup.normalizerMonoidHom H gH) xH ∈ K := hxComap
  exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxImage, by
    simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

/-- Inverted-set cardinality is multiplicative across a `t`-invariant
internal direct product. -/
public theorem proposition102_invertedCard_mul_of_internalDirectProduct
    {X : Type u} [Group X] [Finite X]
    {H A B : Subgroup X} {t : X}
    (hprod : Section2.IsInternalDirectProduct H A B)
    (htnormA : t ∈ Subgroup.normalizer (A : Set X))
    (htnormB : t ∈ Subgroup.normalizer (B : Set X)) :
    theorem4bInvertedCard t H =
      theorem4bInvertedCard t A * theorem4bInvertedCard t B := by
  let IA := {x : X // x ∈ A ∧ t * x * t⁻¹ = x⁻¹}
  let IB := {x : X // x ∈ B ∧ t * x * t⁻¹ = x⁻¹}
  let IH := {x : X // x ∈ H ∧ t * x * t⁻¹ = x⁻¹}
  let f : IA × IB → IH := fun z =>
    ⟨(z.1 : X) * (z.2 : X),
      hprod.left_le z.1.property.1 |> fun haH =>
        ⟨H.mul_mem haH (hprod.right_le z.2.property.1), by
          have hcomm : Commute (z.1 : X) (z.2 : X) :=
            hprod.commute (z.1 : X) z.1.property.1
              (z.2 : X) z.2.property.1
          calc
            t * ((z.1 : X) * (z.2 : X)) * t⁻¹ =
                (t * (z.1 : X) * t⁻¹) *
                  (t * (z.2 : X) * t⁻¹) := by group
            _ = (z.1 : X)⁻¹ * (z.2 : X)⁻¹ := by
              rw [z.1.property.2, z.2.property.2]
            _ = ((z.1 : X) * (z.2 : X))⁻¹ := by
              rw [mul_inv_rev]
              exact hcomm.inv_inv.eq⟩⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hxyX : (x.1 : X) * (x.2 : X) = (y.1 : X) * (y.2 : X) :=
      congrArg (fun z : IH => (z : X)) hxy
    have hAB :
        ((⟨(x.1 : X), x.1.property.1⟩ : A),
          (⟨(x.2 : X), x.2.property.1⟩ : B)) =
        ((⟨(y.1 : X), y.1.property.1⟩ : A),
          (⟨(y.2 : X), y.2.property.1⟩ : B)) :=
      Subgroup.mul_injective_of_disjoint
        (show Disjoint A B by rw [disjoint_iff, hprod.inf_eq_bot]) hxyX
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z : A × B => (z.1 : X)) hAB
    · apply Subtype.ext
      exact congrArg (fun z : A × B => (z.2 : X)) hAB
  have hf_surj : Function.Surjective f := by
    intro x
    rcases hprod.mul_surjective (x : X) x.property.1 with
      ⟨a, haA, b, hbB, hab⟩
    have htaA : t * a * t⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp htnormA a).mp haA
    have htbB : t * b * t⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp htnormB b).mp hbB
    have hainvA : a⁻¹ ∈ A := A.inv_mem haA
    have hbinvB : b⁻¹ ∈ B := B.inv_mem hbB
    have hcompEq :
        (t * a * t⁻¹) * (t * b * t⁻¹) = a⁻¹ * b⁻¹ := by
      calc
        (t * a * t⁻¹) * (t * b * t⁻¹) =
            t * (a * b) * t⁻¹ := by group
        _ = t * (x : X) * t⁻¹ := by rw [hab]
        _ = (x : X)⁻¹ := x.property.2
        _ = (a * b)⁻¹ := by rw [hab]
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = a⁻¹ * b⁻¹ := by
          exact (show Commute a b from
            hprod.commute a haA b hbB).inv_inv.eq.symm
    let lhs : A × B :=
      (⟨t * a * t⁻¹, htaA⟩, ⟨t * b * t⁻¹, htbB⟩)
    let rhs : A × B := (⟨a⁻¹, hainvA⟩, ⟨b⁻¹, hbinvB⟩)
    have hpair : lhs = rhs := by
      apply Subgroup.mul_injective_of_disjoint
        (show Disjoint A B by rw [disjoint_iff, hprod.inf_eq_bot])
      simpa [lhs, rhs] using hcompEq
    have haanti : t * a * t⁻¹ = a⁻¹ :=
      congrArg (fun z : A × B => (z.1 : X)) hpair
    have hbanti : t * b * t⁻¹ = b⁻¹ :=
      congrArg (fun z : A × B => (z.2 : X)) hpair
    let aI : IA := ⟨a, haA, haanti⟩
    let bI : IB := ⟨b, hbB, hbanti⟩
    refine ⟨(aI, bI), ?_⟩
    apply Subtype.ext
    exact hab.symm
  calc
    theorem4bInvertedCard t H = Nat.card IH := rfl
    _ = Nat.card (IA × IB) :=
      Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm
    _ = Nat.card IA * Nat.card IB := Nat.card_prod IA IB
    _ = theorem4bInvertedCard t A * theorem4bInvertedCard t B := rfl

/-- Centralizing a subgroup of the left factor of an internal direct product
preserves the right factor and splits the centralizer internally. -/
public theorem proposition102_centralizer_factor_internalDirectProduct
    {X : Type u} [Group X]
    {H S₁ S₂ R : Subgroup X}
    (hprod : Section2.IsInternalDirectProduct H S₁ S₂)
    (hR : R ≤ S₁) :
    Section2.IsInternalDirectProduct
      (subgroupCentralizerIn H R)
      (subgroupCentralizerIn S₁ R) S₂ := by
  have hS₂cent : S₂ ≤ Subgroup.centralizer (R : Set X) := by
    intro s₂ hs₂
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact hprod.commute r (hR hr) s₂ hs₂
  have hleft : subgroupCentralizerIn S₁ R ≤ subgroupCentralizerIn H R := by
    intro x hx
    exact ⟨hprod.left_le hx.1, hx.2⟩
  have hright : S₂ ≤ subgroupCentralizerIn H R := by
    intro x hx
    exact ⟨hprod.right_le hx, hS₂cent hx⟩
  have hS₂centC : S₂ ≤ Subgroup.centralizer
      (subgroupCentralizerIn S₁ R : Set X) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact hprod.commute c hc.1 s hs
  have hnorm : S₂ ≤ Subgroup.normalizer
      (subgroupCentralizerIn S₁ R : Set X) := by
    intro s hs
    exact centralizer_le_normalizer
      (subgroupCentralizerIn S₁ R) (hS₂centC hs)
  have hcent_sup : subgroupCentralizerIn S₁ R ⊔ S₂ =
      subgroupCentralizerIn H R := by
    apply le_antisymm
    · exact sup_le hleft hright
    · intro x hx
      rcases hprod.mul_surjective x hx.1 with ⟨a, ha, b, hb, hab⟩
      have hba : b ∈ Subgroup.centralizer (R : Set X) := hS₂cent hb
      have haCent : a ∈ Subgroup.centralizer (R : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have hxCent := Subgroup.mem_centralizer_iff.mp hx.2 r hr
        have hxCentAB : r * (a * b) = (a * b) * r := by
          simpa [hab] using hxCent
        have hbr : b * r = r * b :=
          (Subgroup.mem_centralizer_iff.mp hba r hr).symm
        have hxCent' : r * (a * b) * b⁻¹ = (a * b) * r * b⁻¹ :=
          congrArg (fun z : X => z * b⁻¹) hxCentAB
        calc
          r * a = r * (a * b) * b⁻¹ := by simp [mul_assoc]
          _ = (a * b) * r * b⁻¹ := hxCent'
          _ = a * (b * r * b⁻¹) := by group
          _ = a * r := by
            rw [hbr]
            simp
      have haC : a ∈ subgroupCentralizerIn S₁ R := ⟨ha, haCent⟩
      have hset := Subgroup.coe_mul_of_right_le_normalizer_left
        (subgroupCentralizerIn S₁ R) S₂ hnorm
      have hmem : x ∈ (subgroupCentralizerIn S₁ R : Set X) * (S₂ : Set X) :=
        Set.mem_mul.mpr ⟨a, haC, b, hb, hab.symm⟩
      rw [← hset] at hmem
      exact hmem
  exact {
    left_le := hleft
    right_le := hright
    commute := by
      intro a ha b hb
      exact hprod.commute a ha.1 b hb
    inf_eq_bot := by
      apply le_antisymm
      · intro x hx
        have hxinf : x ∈ S₁ ⊓ S₂ := ⟨hx.1.1, hx.2⟩
        simpa [hprod.inf_eq_bot] using hxinf
      · exact bot_le
    mul_surjective := by
      intro x hx
      have hx' : x ∈ subgroupCentralizerIn S₁ R ⊔ S₂ := by
        exact hcent_sup ▸ hx
      have hset := Subgroup.coe_mul_of_right_le_normalizer_left
        (subgroupCentralizerIn S₁ R) S₂ hnorm
      have hxset : x ∈ (subgroupCentralizerIn S₁ R : Set X) * (S₂ : Set X) := by
        rw [← hset]
        exact hx'
      rcases Set.mem_mul.mp hxset with ⟨a, ha, b, hb, hab⟩
      exact ⟨a, ha, b, hb, hab.symm⟩ }

/-- The inverted set of a normalized odd `r`-group has prime-power
cardinality. -/
public theorem proposition102_invertedCard_eq_prime_pow
    {X : Type u} [Group X] [Finite X]
    {r : ℕ} (hr : r.Prime) {S : Subgroup X} {t : X}
    (hSp : IsPGroup r S)
    (ht : IsInvolution t)
    (hSodd : Odd (Nat.card S))
    (htnormS : t ∈ Subgroup.normalizer (S : Set X)) :
    ∃ a : ℕ, theorem4bInvertedCard t S = r ^ a := by
  letI : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, hSn⟩ := hSp.exists_card_eq
  have hcard := theorem4b_card_eq_card_fixed_mul_inverted
    ht hSodd htnormS
  have hdvd : theorem4bInvertedCard t S ∣ r ^ n := by
    rw [← hSn, hcard]
    exact Nat.dvd_mul_left _ _
  obtain ⟨a, _ha, hpow⟩ := (Nat.dvd_prime_pow hr).mp hdvd
  exact ⟨a, hpow⟩

/-- If a nontrivial normalized odd subgroup has no nonidentity `t`-fixed
element, every overgroup has a non-singleton inverted set. -/
public theorem proposition102_invertedCard_ne_one_of_fixed_bot
    {X : Type u} [Group X] [Finite X]
    {C Z : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hZodd : Odd (Nat.card Z))
    (htnormZ : t ∈ Subgroup.normalizer (Z : Set X))
    (hZne : Z ≠ ⊥)
    (hfixed : Z ⊓ Subgroup.centralizer ({t} : Set X) = ⊥)
    (hZC : Z ≤ C) :
    theorem4bInvertedCard t C ≠ 1 := by
  have hcardZ := theorem4b_card_eq_card_fixed_mul_inverted
    ht hZodd htnormZ
  have hinvZ : theorem4bInvertedCard t Z = Nat.card Z := by
    rw [hfixed] at hcardZ
    simpa using hcardZ.symm
  have hZgt : 1 < theorem4bInvertedCard t Z := by
    rw [hinvZ]
    exact (Subgroup.one_lt_card_iff_ne_bot Z).2 hZne
  have hmono := theorem4bInvertedCard_mono (z := t) hZC
  intro hCcard
  rw [hCcard] at hmono
  omega

/-- A nontrivial subgroup of `V` cannot centralize every element of the
Peterfalvi inverted set when `C_V(I)=1`. -/
public theorem proposition102_kset_card_ne_centralizer_card
    {X : Type u} [Group X] [Finite X]
    {D V R : Subgroup X} {t : X}
    (hRV : R ≤ V)
    (hRne : R ≠ ⊥)
    (hVC : V ⊓ Subgroup.centralizer (peterfalviKSet D t) = ⊥) :
    Nat.card {x : X // x ∈ peterfalviKSet D t} ≠
      Nat.card {x : X // x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (R : Set X)} := by
  intro hcard
  let I := {x : X // x ∈ peterfalviKSet D t}
  let C := {x : X // x ∈ peterfalviKSet D t ∧
    x ∈ Subgroup.centralizer (R : Set X)}
  let f : C → I := fun x => ⟨x, x.property.1⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : I => (z : X)) hxy
  have hcardCI : Nat.card C = Nat.card I := by
    simpa [C, I] using hcard.symm
  have hf_surj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).2 ⟨hf_inj, hcardCI⟩).2
  apply hRne
  rw [Subgroup.eq_bot_iff_forall]
  intro r hrR
  have hrCent : r ∈ Subgroup.centralizer (peterfalviKSet D t) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hxI
    obtain ⟨y, hy⟩ := hf_surj ⟨x, hxI⟩
    have hyCent : (y : X) ∈ Subgroup.centralizer (R : Set X) := y.property.2
    have hxy : (y : X) = x := congrArg Subtype.val hy
    have hcomm := Subgroup.mem_centralizer_iff.mp hyCent r hrR
    simpa [hxy] using hcomm.symm
  have hrBot : r ∈ (⊥ : Subgroup X) := by
    rw [← hVC]
    exact ⟨hRV hrR, hrCent⟩
  simpa using hrBot

/-- The numerical core of Proposition 10.2(c).  The numbers `i1` and `ci1`
are the inverted cardinalities in the Sylow `r`-factor and its centralizer;
`i2` is the inverted cardinality of the complementary Hall factor. -/
public theorem proposition102_exponent_arithmetic
    {r m q i1 ci1 i2 : ℕ}
    (hr : r.Prime)
    (hi1pow : ∃ b : ℕ, i1 = r ^ b)
    (hci1pow : ∃ c : ℕ, ci1 = r ^ c)
    (hci1_dvd_i1 : ci1 ∣ i1)
    (hmul : m = i1 * i2)
    (hqmul : q = ci1 * i2)
    (hm_ne_q : m ≠ q)
    (hrci1 : r ∣ ci1) :
    ∃ a : ℕ, 1 ≤ a ∧ m = r ^ a * q ∧ r ∣ q := by
  obtain ⟨b, rfl⟩ := hi1pow
  obtain ⟨c, hci1⟩ := hci1pow
  have hci1_dvd_pow : ci1 ∣ r ^ b := hci1_dvd_i1
  obtain ⟨k, hkb, hcik⟩ := (Nat.dvd_prime_pow hr).mp hci1_dvd_pow
  have hkc : k = c := by
    rw [hci1] at hcik
    exact Nat.pow_right_injective hr.two_le hcik.symm
  subst k
  let a : ℕ := b - c
  have hpow : r ^ b = r ^ a * r ^ c := by
    rw [← Nat.pow_add, show a + c = b by
      simpa [a] using Nat.sub_add_cancel hkb]
  have hformula : m = r ^ a * q := by
    calc
      m = r ^ b * i2 := hmul
      _ = (r ^ a * r ^ c) * i2 := by rw [hpow]
      _ = r ^ a * (r ^ c * i2) := by ac_rfl
      _ = r ^ a * (ci1 * i2) := by rw [hci1]
      _ = r ^ a * q := by rw [hqmul]
  have ha_pos : 1 ≤ a := by
    by_contra ha
    have ha0 : a = 0 := by omega
    apply hm_ne_q
    simpa [ha0] using hformula
  refine ⟨a, ha_pos, hformula, ?_⟩
  rw [hqmul]
  exact dvd_mul_of_dvd_left hrci1 i2

end CFSG.BenderSuzuki
