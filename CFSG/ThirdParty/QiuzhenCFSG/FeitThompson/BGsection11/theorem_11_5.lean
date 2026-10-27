module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.corollary_11_4
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

/-!
# Theorem 11.5

This file contains the Section 11 Theorem 11.5 statement and proof.
-/

section Section11

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_not_isCyclic_of_rank_two
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p A] (hcard : Nat.card A = p ^ 2) :
    ¬ IsCyclic A := by
  intro hcyc
  have hdiv : p ^ 2 ∣ p ^ 1 := by
    simpa [hcard] using (show Nat.card A ∣ p from by
      rw [← hcyc.exponent_eq_card]
      exact IsElementaryAbelian.exponent_dvd_p p A)
  have hp_one_lt : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have : 2 ≤ 1 :=
    (Nat.pow_le_pow_iff_right hp_one_lt).mp (Nat.le_of_dvd (by positivity) hdiv)
  omega

omit [IsMinCE G] in
private theorem CFSG.section11_exists_nontrivial_zpowers_fixedPoint_nonbot
    {A H : Type*} [Group A] [Finite A] [Group H] [Finite H] [MulDistribMulAction A H]
    [Nontrivial H]
    (hSup : (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) H) = ⊤) :
    ∃ a : A, a ≠ 1 ∧ fixedPointSubgroup (↥(Subgroup.zpowers a)) H ≠ ⊥ := by
  by_contra h
  have hall :
      ∀ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) H = ⊥ := by
    intro a ha
    by_contra hi
    exact h ⟨a, ha, hi⟩
  have hle_bot :
      (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) H) ≤ ⊥ := by
    refine iSup_le ?_
    intro a
    refine iSup_le ?_
    intro ha
    simp [hall a ha]
  have hbot :
      (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) H) = ⊥ :=
    le_antisymm hle_bot bot_le
  exact top_ne_bot (hSup.symm.trans hbot)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_subgroupCentralizerIn_zpowers_eq_elementCentralizerIn
    {Q : Subgroup G} (a : G) :
    subgroupCentralizerIn Q (Subgroup.zpowers a) = elementCentralizerIn Q a := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr <| by
      have hxcent : x ∈ Subgroup.centralizer ((Subgroup.zpowers a) : Set G) := hx.2
      have hcomm : a * x = x * a :=
        Subgroup.mem_centralizer_iff.mp hxcent a (Subgroup.mem_zpowers a)
      exact hcomm.symm
  · intro hx
    refine ⟨hx.1, ?_⟩
    change x ∈ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with ⟨n, rfl⟩
    have hcomm : Commute x a := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    exact (hcomm.zpow_right n).symm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_zpowers_mem_prime_order_subgroups
    {A : Subgroup G} {p : Nat.Primes} (a : A) (ha_ne : a ≠ 1)
    [IsElementaryAbelian p.val A] :
    Subgroup.zpowers (a : G) ∈ section10PrimeOrderSubgroupsIn p A := by
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hpowA : a ^ p.val = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p.val A) a
  have hpowG : (a : G) ^ p.val = 1 := by
    simpa using congrArg Subtype.val hpowA
  have haG_ne : (a : G) ≠ 1 := by
    intro h
    exact ha_ne (Subtype.ext h)
  have horder : orderOf (a : G) = p.val := orderOf_eq_prime hpowG haG_ne
  refine ⟨?_, ?_⟩
  · exact (Subgroup.zpowers_le).2 a.property
  · simp [Nat.card_zpowers, horder]

omit [IsMinCE G] in
private theorem CFSG.section11_exists_prime_order_subgroup_centralizer_ne_bot
    {M A0 A Q : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P)
    (hQσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Q)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hQ_ne_bot : Q ≠ ⊥) :
    ∃ X ∈ section10PrimeOrderSubgroupsIn p A,
      subgroupCentralizerIn Q X ≠ ⊥ := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases h11.A_rank_two with ⟨hAcard, hAelem⟩
  letI : IsElementaryAbelian p.val A := hAelem
  letI : IsMulCommutative A := hAelem.toIsMulCommutative
  letI : CommGroup A := IsMulCommutative.instCommGroup
  haveI : Fact (IsPGroup p.val A) := ⟨IsElementaryAbelian.isPGroup p.val A⟩
  haveI : Subgroup.Normalizes A Q := ⟨hAQ⟩
  have hcopAQ : Nat.Coprime (Nat.card A) (Nat.card Q) :=
    section11_coprime_A_of_isPiSubgroup_sigma h11 hQσ
  have hp_dvd_A : p.val ∣ Nat.card A := by
    rw [hAcard, pow_two]
    exact dvd_mul_right p.val p.val
  have hcop_p_Q : Nat.Coprime p.val (Nat.card Q) :=
    hcopAQ.coprime_dvd_left hp_dvd_A
  have hQ_nontrivial : Nontrivial Q := by
    exact Q.nontrivial_iff_ne_bot.mpr hQ_ne_bot
  letI : Nontrivial Q := hQ_nontrivial
  have hsup :
      (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) Q) =
        ⊤ :=
    proposition_1_16_a (G := Q) (A := A) p.val hcop_p_Q
      (section11_not_isCyclic_of_rank_two (p := p.val) hAcard)
  obtain ⟨a, ha_ne, hfix_ne_bot⟩ :=
    section11_exists_nontrivial_zpowers_fixedPoint_nonbot (A := A) (H := Q) hsup
  have hfix_eq :
      fixedPointSubgroup (↥(Subgroup.zpowers a)) Q =
        (elementCentralizerIn Q (a : G)).subgroupOf Q := by
    simpa using
      fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn
        (K := Q) (R := A) hAQ a
  refine ⟨Subgroup.zpowers (a : G),
    section11_zpowers_mem_prime_order_subgroups (p := p) a ha_ne, ?_⟩
  have hcent_sub_ne_bot :
      (elementCentralizerIn Q (a : G)).subgroupOf Q ≠ ⊥ := by
    simpa [hfix_eq] using hfix_ne_bot
  have hcent_ne_bot : elementCentralizerIn Q (a : G) ≠ ⊥ := by
    intro hbot
    have hsub_bot :
        (elementCentralizerIn Q (a : G)).subgroupOf Q = ⊥ := by
      simp [hbot]
    exact hcent_sub_ne_bot hsub_bot
  simpa [section11_subgroupCentralizerIn_zpowers_eq_elementCentralizerIn]
    using hcent_ne_bot

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_normalizer_le_normalizer_map_subtype_of_characteristic
    (H : Subgroup G) (K : Subgroup H) [K.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (((K : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  classical
  refine subgroup_le_normalizer_of_conj_mem ((K : Subgroup H).map H.subtype)
    (Subgroup.normalizer (H : Set G)) ?_
  intro g x hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, hxK, rfl⟩
  let gH : Subgroup.normalizer (H : Set G) := ⟨g, by simp⟩
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K = K :=
    (inferInstance : K.Characteristic).fixed (Subgroup.normalizerMonoidHom H gH)
  have hxComap :
      xH ∈ Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K := by
    rw [hfix]
    exact hxK
  have hxImage : (Subgroup.normalizerMonoidHom H gH) xH ∈ K := hxComap
  exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxImage, by
    simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

omit [IsMinCE G] in
public theorem CFSG.section11_isMulCommutative_sylow_of_sylow
    {p : Nat.Primes} (P Q : Sylow p.val G)
    (hP : IsMulCommutative (P : Subgroup G)) :
    IsMulCommutative (Q : Subgroup G) := by
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let e : P ≃* Q := Sylow.equiv P Q
  refine Subgroup.le_centralizer_iff_isMulCommutative.mp ?_
  intro x hx y hy
  let xQ : Q := ⟨x, hx⟩
  let yQ : Q := ⟨y, hy⟩
  let xP : P := e.symm xQ
  let yP : P := e.symm yQ
  have hcommP : xP * yP = yP * xP := by
    exact (IsMulCommutative.is_comm (M := (P : Subgroup G))).comm xP yP
  have hcommQ : xQ * yQ = yQ * xQ := by
    simpa [xP, yP, xQ, yQ] using congrArg e hcommP
  exact (congrArg Subtype.val hcommQ).symm

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_subgroupCentralizerIn_conjBy
    (R X : Subgroup G) (g : G) :
    subgroupCentralizerIn (R.conjBy g) (X.conjBy g) =
      (subgroupCentralizerIn R X).conjBy g := by
  ext y
  constructor
  · intro hy
    rcases hy.1 with ⟨r, hrR, hry⟩
    refine Subgroup.mem_map.mpr ⟨r, ?_, hry⟩
    refine ⟨hrR, ?_⟩
    change r ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hxX
    have hxg : g * x * g⁻¹ ∈ X.conjBy g := Subgroup.mem_map.mpr ⟨x, hxX, rfl⟩
    have hcommg : (g * x * g⁻¹) * y = y * (g * x * g⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hy.2 (g * x * g⁻¹) hxg
    have hry' : y = g * r * g⁻¹ := by simpa [MulAut.conj_apply] using hry.symm
    have hconj : g * (x * r) * g⁻¹ = g * (r * x) * g⁻¹ := by
      calc
        g * (x * r) * g⁻¹ = (g * x * g⁻¹) * y := by
          rw [hry']
          group
        _ = y * (g * x * g⁻¹) := hcommg
        _ = g * (r * x) * g⁻¹ := by
          rw [hry']
          group
    exact (MulAut.conj g).injective hconj
  · intro hy
    rcases hy with ⟨r, hr, hry⟩
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨r, hr.1, hry⟩
    · change y ∈ Subgroup.centralizer (X.conjBy g : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro x hxXg
      rcases hxXg with ⟨x0, hx0X, hx0x⟩
      have hcomm : x0 * r = r * x0 :=
        Subgroup.mem_centralizer_iff.mp hr.2 x0 hx0X
      have hry' : y = g * r * g⁻¹ := by simpa [MulAut.conj_apply] using hry.symm
      have hx' : x = g * x0 * g⁻¹ := by simpa [MulAut.conj_apply] using hx0x.symm
      calc
        x * y = (g * x0 * g⁻¹) * (g * r * g⁻¹) := by rw [hx', hry']
        _ = g * (x0 * r) * g⁻¹ := by group
        _ = g * (r * x0) * g⁻¹ := by rw [hcomm]
        _ = (g * r * g⁻¹) * (g * x0 * g⁻¹) := by group
        _ = y * x := by rw [hx', hry']

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_conjBy_ne_bot
    {H : Subgroup G} {g : G} (hH : H ≠ ⊥) :
    H.conjBy g ≠ ⊥ := by
  intro hbot
  have hcard_map : Nat.card (H.conjBy g) = Nat.card H :=
    section11_card_conjBy H g
  have hcardH : Nat.card H = 1 := by
    rw [← hcard_map]
    simp [hbot]
  exact hH ((Subgroup.card_eq_one (H := H)).1 hcardH)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_subgroupCentralizerIn_conjBy_ne_bot
    {R X : Subgroup G} {g : G}
    (hC : subgroupCentralizerIn R X ≠ ⊥) :
    subgroupCentralizerIn (R.conjBy g) (X.conjBy g) ≠ ⊥ := by
  rw [section11_subgroupCentralizerIn_conjBy]
  exact section11_conjBy_ne_bot hC

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_subgroupCentralizerIn_conjBy_eq_self_of_mem_normalizer
    {R X : Subgroup G} {g : G}
    (hgR : g ∈ Subgroup.normalizer (R : Set G)) :
    subgroupCentralizerIn R (X.conjBy g) =
      (subgroupCentralizerIn R X).conjBy g := by
  have hR : R.conjBy g = R := section11_conjBy_eq_of_mem_normalizer hgR
  simpa [hR] using section11_subgroupCentralizerIn_conjBy R X g

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_subgroupCentralizerIn_conjBy_self_ne_bot_of_mem_normalizer
    {R X : Subgroup G} {g : G}
    (hgR : g ∈ Subgroup.normalizer (R : Set G))
    (hC : subgroupCentralizerIn R X ≠ ⊥) :
    subgroupCentralizerIn R (X.conjBy g) ≠ ⊥ := by
  rw [section11_subgroupCentralizerIn_conjBy_eq_self_of_mem_normalizer hgR]
  exact section11_conjBy_ne_bot hC

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_omega1Z_characteristic
    (p : Nat.Primes) (P : Subgroup G) :
    (Ω₁Z p.val P).Characteristic := by
  let C : Subgroup P := Subgroup.center P
  let Ω : Subgroup C := omega₁ (G := C) (p := p.val)
  letI : C.Characteristic := Subgroup.centerCharacteristic
  letI : Ω.Characteristic := by
    simpa [Ω] using omega₁_characteristic (G := C) (p := p.val)
  simpa [Ω₁Z, C, Ω] using
    (characteristic_map_subtype_of_characteristic (G := P) C Ω)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_normalizer_le_normalizer_omegaOneCenter
    (p : Nat.Primes) (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (section10OmegaOneCenter p P : Set G) := by
  letI : (Ω₁Z p.val P).Characteristic := section11_omega1Z_characteristic p P
  simpa [section10OmegaOneCenter] using
    section11_normalizer_le_normalizer_map_subtype_of_characteristic
      (G := G) P (Ω₁Z p.val P)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_normalizer_le_normalizer_omegaOne
    (p : Nat.Primes) (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (section11OmegaOne p P : Set G) := by
  let Ω : Subgroup P := omega₁ (G := P) (p := p.val)
  letI : Ω.Characteristic := by
    simpa [Ω] using omega₁_characteristic (G := P) (p := p.val)
  simpa [section11OmegaOne, Ω] using
    section11_normalizer_le_normalizer_map_subtype_of_characteristic
      (G := G) P Ω


omit [IsMinCE G] in
public theorem CFSG.section11_ambientSylow_ne_bot_of_prime_dvd
    {H : Subgroup G} {q : Nat.Primes} (Q : Sylow q.val H)
    (hqH : q.val ∣ Nat.card H) :
    section10AmbientSylowSubgroup H Q ≠ ⊥ := by
  haveI : Fact q.val.Prime := ⟨q.property⟩
  have hQ_ne : (Q : Subgroup H) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := H) (p := q.val) Q hqH
  intro hbot
  have hcard_map :
      Nat.card (section10AmbientSylowSubgroup H Q) = Nat.card (Q : Subgroup H) := by
    simpa [section10AmbientSylowSubgroup] using
      (Subgroup.card_map_of_injective
        (K := (Q : Subgroup H)) (f := H.subtype) H.subtype_injective)
  have hQ_card : Nat.card (Q : Subgroup H) = 1 := by
    rw [← hcard_map]
    simp [hbot]
  exact hQ_ne ((Subgroup.card_eq_one (H := (Q : Subgroup H))).1 hQ_card)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_isMulCommutative_sylow_of_ambient
    {M : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (hcomm : IsMulCommutative (section10AmbientSylowSubgroup M P)) :
    IsMulCommutative (P : Subgroup M) := by
  refine Subgroup.le_centralizer_iff_isMulCommutative.mp ?_
  intro x hx y hy
  have hxamb : ((x : M) : G) ∈ section10AmbientSylowSubgroup M P := by
    exact Subgroup.mem_map.mpr ⟨(⟨x, hx⟩ : P), (⟨x, hx⟩ : P).property, rfl⟩
  have hyamb : ((y : M) : G) ∈ section10AmbientSylowSubgroup M P := by
    exact Subgroup.mem_map.mpr ⟨(⟨y, hy⟩ : P), (⟨y, hy⟩ : P).property, rfl⟩
  have hcommG :
      ((x : M) : G) * ((y : M) : G) = ((y : M) : G) * ((x : M) : G) := by
    simpa using congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := section10AmbientSylowSubgroup M P)).comm
        ⟨((x : M) : G), hxamb⟩ ⟨((y : M) : G), hyamb⟩)
  apply Subtype.ext
  exact hcommG.symm

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_isMulCommutative_ambient_of_sylow
    {M : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (hcomm : IsMulCommutative (P : Subgroup M)) :
    IsMulCommutative (section10AmbientSylowSubgroup M P) := by
  letI : IsMulCommutative (P : Subgroup M) := hcomm
  change IsMulCommutative ((P : Subgroup M).map M.subtype)
  exact Subgroup.map_isMulCommutative (f := M.subtype) (H := (P : Subgroup M))

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_omega1_isElementaryAbelian_of_commutative
    {p : ℕ} [Fact p.Prime]
    (H : Type*) [Group H] [IsMulCommutative H] :
    IsElementaryAbelian p (omega₁ (G := H) (p := p)) := by
  letI : CommGroup H := IsMulCommutative.instCommGroup
  refine
    { toIsMulCommutative := by infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  exact
    Subgroup.closure_induction (k := {y : H | y ^ (p ^ 1) = 1})
      (p := fun z _hz => z ^ p = 1) (x := x) (by
        intro y hy
        simpa [pow_one] using hy) (by simp) (by
        intro y z _ _ hy hz
        calc
          (y * z) ^ p = y ^ p * z ^ p := by
            simpa using mul_pow y z p
          _ = 1 := by simp [hy, hz]) (by
        intro y _ hy
        simp [hy]) x.property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section11_isElementaryAbelian_map
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} [IsElementaryAbelian p A]
    {G' : Type*} [Group G'] (f : G →* G') :
    IsElementaryAbelian p (A.map f) := by
  refine
    { toIsMulCommutative := by
        simpa using (Subgroup.map_isMulCommutative (f := f) (H := A))
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  rcases Subgroup.mem_map.mp x.2 with ⟨y, hyA, hyx⟩
  let yA : A := ⟨y, hyA⟩
  have hypow : yA ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p A) yA
  have hx_eq : (x : G') = f y := by simpa using hyx.symm
  calc
    (x : G') ^ p = (f y) ^ p := by simp [hx_eq]
    _ = f (y ^ p) := by simp
    _ = 1 := by simpa using congrArg f (congrArg Subtype.val hypow)

/-- Theorem 11.5. -/
public theorem CFSG.theorem_11_5
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    ∀ P' : Sylow p.val M, IsMulCommutative (P' : Subgroup M) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let Pamb : Subgroup G := section10AmbientSylowSubgroup M P
  have hPamb_le_M : Pamb ≤ M := by
    simpa [Pamb] using section11_ambientSylow_le M P
  have hpG : p ∈ subgroupPrimeSet (⊤ : Subgroup G) := by
    rcases h11.A_rank_two with ⟨hAcard, _hAelem⟩
    have hpA : p.val ∣ Nat.card A := by
      rw [hAcard, pow_two]
      exact dvd_mul_right p.val p.val
    have hpG' : p.val ∣ Nat.card G :=
      hpA.trans (Subgroup.card_subgroup_dvd_card A)
    simpa [subgroupPrimeSet] using hpG'
  have hPamb_comm : IsMulCommutative Pamb := by
    by_contra hPamb_nonab
    obtain ⟨g, hgN, hgM, hA_le_Mg⟩ := section11_obtain_g_and_A_le_Mg h11
    have hgN' : g ∈ Subgroup.normalizer (Pamb : Set G) := by simpa [Pamb] using hgN
    let K : Subgroup G := section10Msigma M
    have hK_ne : K ≠ ⊥ := by
      simpa [K] using theorem_10_2_e h11.maximal
    have hK_card_ne_one : Nat.card K ≠ 1 := by
      intro hcard
      exact hK_ne ((Subgroup.card_eq_one (H := K)).1 hcard)
    obtain ⟨q0, hq0prime, hq0dvd⟩ := Nat.exists_prime_and_dvd hK_card_ne_one
    let q : Nat.Primes := ⟨q0, hq0prime⟩
    haveI : Fact q.val.Prime := ⟨q.property⟩
    have hqK : q.val ∣ Nat.card K := by
      simpa [q] using hq0dvd
    have hqσ : q ∈ section10SigmaPrimes M := by
      exact (theorem_10_2_b h11.maximal).1.p_in_pi_of_p_dvd_card q (by
        simpa [K] using hqK)
    let Q1 : Sylow q.val K :=
      Classical.choice (inferInstance : Nonempty (Sylow q.val K))
    let R1 : Subgroup G := section10AmbientSylowSubgroup K Q1
    have hnilK : Group.IsNilpotent K := by
      simpa [K] using theorem_11_3 h11
    have hQ1_normal : ((Q1 : Subgroup K)).Normal :=
      Group.IsNilpotent.sylow_normal hnilK q.val Q1
    have hQ1_char : ((Q1 : Subgroup K)).Characteristic :=
      Sylow.characteristic_of_normal Q1 hQ1_normal
    letI : ((Q1 : Subgroup K)).Characteristic := hQ1_char
    have hA_norm_K : A ≤ Subgroup.normalizer (K : Set G) :=
      h11.A_le_M.trans (by simpa [K] using section11_msigma_le_normalizer M)
    have hM_norm_K : M ≤ Subgroup.normalizer (K : Set G) := by
      simpa [K] using section11_msigma_le_normalizer M
    have hAQ1 : A ≤ Subgroup.normalizer (R1 : Set G) := by
      exact hA_norm_K.trans (by
        simpa [R1, section10AmbientSylowSubgroup] using
          section11_normalizer_le_normalizer_map_subtype_of_characteristic
            (G := G) K (Q1 : Subgroup K))
    have hPamb_norm_R1 : Pamb ≤ Subgroup.normalizer (R1 : Set G) := by
      exact (hPamb_le_M.trans hM_norm_K).trans (by
        simpa [R1, section10AmbientSylowSubgroup] using
          section11_normalizer_le_normalizer_map_subtype_of_characteristic
            (G := G) K (Q1 : Subgroup K))
    let Kg : Subgroup G := K.conjBy g
    obtain ⟨Q2, hQ2_eq⟩ :
        ∃ Q2 : Sylow q.val Kg,
          section10AmbientSylowSubgroup Kg Q2 = R1.conjBy g := by
      simpa [K, Kg, R1] using section11_ambientSylow_conjBy_exists K Q1 g
    let R2 : Subgroup G := section10AmbientSylowSubgroup Kg Q2
    have hR2_eq : R2 = R1.conjBy g := by
      simpa [R2] using hQ2_eq
    have hnilKg : Group.IsNilpotent Kg := by
      let e : K ≃* Kg := (MulAut.conj g).subgroupMap K
      exact Group.nilpotent_of_mulEquiv (G := K) (G' := Kg) (_h := hnilK) e
    have hQ2_normal : ((Q2 : Subgroup Kg)).Normal :=
      Group.IsNilpotent.sylow_normal hnilKg q.val Q2
    have hQ2_char : ((Q2 : Subgroup Kg)).Characteristic :=
      Sylow.characteristic_of_normal Q2 hQ2_normal
    letI : ((Q2 : Subgroup Kg)).Characteristic := hQ2_char
    have hMg_norm_Kg : M.conjBy g ≤ Subgroup.normalizer (Kg : Set G) := by
      simpa [K, Kg] using
        section11_conjBy_le_normalizer_conjBy_of_le_normalizer
          (section11_msigma_le_normalizer M) g
    have hA_norm_Kg : A ≤ Subgroup.normalizer (Kg : Set G) :=
      hA_le_Mg.trans hMg_norm_Kg
    have hAQ2 : A ≤ Subgroup.normalizer (R2 : Set G) := by
      exact hA_norm_Kg.trans (by
        simpa [R2, section10AmbientSylowSubgroup] using
          section11_normalizer_le_normalizer_map_subtype_of_characteristic
            (G := G) Kg (Q2 : Subgroup Kg))
    have hKσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) K := by
      have hHallK : IsHallSubgroup (section10SigmaPrimes M) K := by
        simpa [K] using (theorem_10_2_b h11.maximal).1
      exact hHallK.p_in_pi_of_p_dvd_card
    have hR1σ : IsPiSubgroup (G := G) (section10SigmaPrimes M) R1 := by
      exact IsPiSubgroup.of_le (by
        simpa [R1] using section11_ambientSylow_le K Q1) hKσ
    have hHallKg : IsHallSubgroup (section10SigmaPrimes M) Kg := by
      simpa [K, Kg, Subgroup.conjBy] using (theorem_10_2_b h11.maximal).1.map_conj g
    have hKgσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Kg :=
      hHallKg.p_in_pi_of_p_dvd_card
    have hR2σ : IsPiSubgroup (G := G) (section10SigmaPrimes M) R2 := by
      exact IsPiSubgroup.of_le (by
        simpa [R2] using section11_ambientSylow_le Kg Q2) hKgσ
    have hR1_ne : R1 ≠ ⊥ := by
      simpa [R1] using section11_ambientSylow_ne_bot_of_prime_dvd
        (G := G) (H := K) (q := q) Q1 hqK
    have hR2_ne : R2 ≠ ⊥ := by
      rw [hR2_eq]
      exact section11_conjBy_ne_bot hR1_ne
    obtain ⟨X1, hX1, hC1ne⟩ :=
      section11_exists_prime_order_subgroup_centralizer_ne_bot
        (M := M) (A0 := A0) (A := A) (p := p) (P := P) h11 hR1σ hAQ1 hR1_ne
    obtain ⟨X2, hX2, hC2ne⟩ :=
      section11_exists_prime_order_subgroup_centralizer_ne_bot
        (M := M) (A0 := A0) (A := A) (p := p) (P := P) h11 hR2σ hAQ2 hR2_ne
    have hC1X2_bot : subgroupCentralizerIn R1 X2 = ⊥ := by
      have hC_or :=
        lemma_11_1_b (M := M) (A0 := A0) (A := A) (p := p) (P := P)
          h11 (g := g) hgM hA_le_Mg hqσ Q1 Q2 hAQ1 hAQ2 hX2
      rcases hC_or with hbot | hbot
      · simpa [K, Kg, R1] using hbot
      · exact False.elim (hC2ne (by simpa [Kg, R2] using hbot))
    have hnot_conj :
        ¬ ∃ k : subgroupNormalizerIn Pamb (A : Set G), X2 = X1.conjBy (k : G) := by
      rintro ⟨k, hk⟩
      have hkPamb : (k : G) ∈ Pamb := (mem_subgroupNormalizerIn.mp k.2).2
      have hkR1 : (k : G) ∈ Subgroup.normalizer (R1 : Set G) :=
        hPamb_norm_R1 hkPamb
      have hC1X2_ne : subgroupCentralizerIn R1 X2 ≠ ⊥ := by
        rw [hk]
        exact section11_subgroupCentralizerIn_conjBy_self_ne_bot_of_mem_normalizer
          hkR1 hC1ne
      exact hC1X2_ne hC1X2_bot
    let Ω : Subgroup G := section10OmegaOneCenter p Pamb
    have hX1_or_X2_Ω : X1 = Ω ∨ X2 = Ω := by
      by_cases hX1Ω : X1 = Ω
      · exact Or.inl hX1Ω
      by_cases hX2Ω : X2 = Ω
      · exact Or.inr hX2Ω
      have htrans :
          ConjugationActionTransitiveOn (subgroupNormalizerIn Pamb (A : Set G))
            {X | X ∈ section10PrimeOrderSubgroupsIn p A ∧ X ≠ Ω} := by
        simpa [Pamb, Ω] using
          lemma_10_13_c (G := G) (p := p) (A := A) (P := Pamb) (A₀ := X1)
            hpG h11.rankTwoMaximal
            (by simpa [Pamb] using section11_ambientSylow_isPGroup M P)
            hPamb_nonab h11.A_le_ambient_sylow hX1 (by simpa [Ω] using hX1Ω)
      obtain ⟨k, hk⟩ := htrans X1 ⟨hX1, hX1Ω⟩ X2 ⟨hX2, hX2Ω⟩
      exact False.elim (hnot_conj ⟨k, hk⟩)
    have hgΩ : g ∈ Subgroup.normalizer (Ω : Set G) := by
      exact section11_normalizer_le_normalizer_omegaOneCenter p Pamb hgN'
    have hΩ_conj : Ω.conjBy g = Ω :=
      section11_conjBy_eq_of_mem_normalizer hgΩ
    have hΩ_conj_inv : Ω.conjBy g⁻¹ = Ω :=
      section11_conjBy_eq_of_mem_normalizer
        (Subgroup.inv_mem (Subgroup.normalizer (Ω : Set G)) hgΩ)
    rcases hX1_or_X2_Ω with hX1Ω | hX2Ω
    · have hΩmem : Ω ∈ section10PrimeOrderSubgroupsIn p A := by
        simpa [Ω, hX1Ω] using hX1
      have hC1Ωne : subgroupCentralizerIn R1 Ω ≠ ⊥ := by
        simpa [Ω, hX1Ω] using hC1ne
      have hC2Ωne : subgroupCentralizerIn R2 Ω ≠ ⊥ := by
        have htmp :=
          section11_subgroupCentralizerIn_conjBy_ne_bot
            (G := G) (R := R1) (X := Ω) (g := g) hC1Ωne
        simpa [hR2_eq, hΩ_conj] using htmp
      have hC_or :=
        lemma_11_1_b (M := M) (A0 := A0) (A := A) (p := p) (P := P)
          h11 (g := g) hgM hA_le_Mg hqσ Q1 Q2 hAQ1 hAQ2 hΩmem
      rcases hC_or with hbot | hbot
      · exact hC1Ωne (by simpa [K, Kg, R1] using hbot)
      · exact hC2Ωne (by simpa [Kg, R2] using hbot)
    · have hΩmem : Ω ∈ section10PrimeOrderSubgroupsIn p A := by
        simpa [Ω, hX2Ω] using hX2
      have hC2Ωne : subgroupCentralizerIn R2 Ω ≠ ⊥ := by
        simpa [Ω, hX2Ω] using hC2ne
      have hC1Ωne : subgroupCentralizerIn R1 Ω ≠ ⊥ := by
        have htmp :=
          section11_subgroupCentralizerIn_conjBy_ne_bot
            (G := G) (R := R2) (X := Ω) (g := g⁻¹) hC2Ωne
        simpa [hR2_eq, section11_conjBy_inv R1 g, hΩ_conj_inv] using htmp
      have hC_or :=
        lemma_11_1_b (M := M) (A0 := A0) (A := A) (p := p) (P := P)
          h11 (g := g) hgM hA_le_Mg hqσ Q1 Q2 hAQ1 hAQ2 hΩmem
      rcases hC_or with hbot | hbot
      · exact hC1Ωne (by simpa [K, Kg, R1] using hbot)
      · exact hC2Ωne (by simpa [Kg, R2] using hbot)
  intro P'
  have hP_comm : IsMulCommutative (P : Subgroup M) :=
    section11_isMulCommutative_sylow_of_ambient (G := G) hPamb_comm
  exact section11_isMulCommutative_sylow_of_sylow (G := M) P P' hP_comm

end Section11
