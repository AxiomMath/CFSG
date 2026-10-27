module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2QuotientTorusCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseReflectedTorusNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4, equation (9): `S₀` lies in the quotient torus

This module discharges the `hS0leT` prerequisite of
`SecondCaseLinearEquationNineData`: once the ambient Sylow lies in the
component (`S ⊆ E`), the image of the cyclic subgroup `S₀` (the index-two
rotation half of the dihedral Sylow `S`, containing the involution `t`) in
`E / Z(E)` lies in the reflected torus `T` of
`SecondCasePSL2QuotientTorusCard`.

The dihedral structure of `C_{L₂(q)}(t)` — `C(t) = T ⊔ ⟨s⟩` with the
reflection `s` inverting the torus `T` — is re-derived at the `PSL₂(K)`
level from the Huppert reflected-normalizer data (`psl2_reflected_join`),
then transported through the model equivalence.  Every cyclic subgroup of
`C(t)` containing `t` lies in the torus: an element outside the torus is a
reflection `u·s` (an involution), and a cyclic group has at most one
involution (`cyclic_unique_involution`).
-/

noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki.External

universe u

/-! ## Cyclic groups have at most one involution -/

private theorem cyclic_unique_involution {A : Type u} [Group A] [Finite A]
    (hcyc : IsCyclic A) : ∀ x y : A, x ≠ 1 → x ^ 2 = 1 → y ≠ 1 → y ^ 2 = 1 → x = y := by
  classical
  let : IsCyclic A := hcyc
  intro x y hx1 hx2 hy1 hy2
  let : Fintype A := Fintype.ofFinite A
  by_contra hxy
  let S : Finset A := {1, x, y}
  have hSsub : S ⊆ ({z : A | z ^ 2 = 1} : Finset A) := by
    intro z hz
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · simp
    · simpa using hx2
    · simpa using hy2
  have hcard : S.card ≤ 2 :=
    le_trans (Finset.card_le_card hSsub)
      (IsCyclic.card_pow_eq_one_le (α := A) (n := 2) (by norm_num))
  have h1x : (1 : A) ≠ x := fun h => hx1 h.symm
  have h1y : (1 : A) ≠ y := fun h => hy1 h.symm
  have hbad : 3 ≤ 2 := by
    simpa [S, h1x, h1y, hx1, hy1, hxy] using hcard
  omega

/-- A power (natural exponent) of an involution is trivial or the
involution itself. -/
private theorem pow_of_involution {G : Type u} [Group G] {s : G}
    (hs2 : s ^ 2 = 1) (k : ℕ) : s ^ k = 1 ∨ s ^ k = s := by
  rcases Nat.even_or_odd k with ⟨j, hk⟩ | ⟨j, hk⟩
  · left
    rw [hk, ← two_mul j, pow_mul, hs2, one_pow]
  · right
    rw [hk, pow_succ, pow_mul, hs2]
    simp

/-- A power (integer exponent) of an involution is trivial or the
involution itself. -/
private theorem zpow_of_involution {G : Type u} [Group G] {s : G}
    (hsI : IsInvolution s) (n : ℤ) : s ^ n = 1 ∨ s ^ n = s := by
  have hs2 : s ^ 2 = 1 := hsI.2
  have hss : s⁻¹ = s :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hs2)
  rcases n with n | n
  · rcases pow_of_involution hs2 n with h | h
    · left
      simpa [zpow_natCast] using h
    · right
      simpa [zpow_natCast] using h
  · rcases pow_of_involution hs2 (n + 1) with h | h
    · left
      rw [zpow_negSucc, h]
      simp
    · right
      rw [zpow_negSucc, h]
      rw [hss]

/-! ## The cyclic containment lemma for a reflected dihedral pair -/

/-- A cyclic subgroup of `C(t)` containing the involution `t` lies in the
rotation torus. -/
private theorem cyclic_subgroup_containing_involution_le_torus
    {G : Type u} [Group G] [Finite G]
    {t : G} (ht : IsInvolution t)
    (T : Subgroup G) (s : G)
    (hTcyc : IsCyclic T) (htT : t ∈ T)
    (hsI : IsInvolution s) (hs_not_T : s ∉ T)
    (hinvT : ∀ x : G, x ∈ T → s * x * s⁻¹ = x⁻¹)
    (hC : Subgroup.centralizer ({t} : Set G) = T ⊔ Subgroup.zpowers s)
    {X : Subgroup G} (hXcyc : IsCyclic X)
    (hXcent : X ≤ Subgroup.centralizer ({t} : Set G))
    (htX : t ∈ X) :
    X ≤ T := by
  exact cyclic_subgroup_containing_involution_le_reflected_torus
    ht T s hTcyc htT hsI hs_not_T hinvT hC hXcyc hXcent htX

/-- The join of the torus and a reflection has twice the torus order. -/
private theorem join_card_of_inverting_reflection {G : Type u} [Group G] [Finite G]
    {T : Subgroup G} {s : G}
    (hsI : IsInvolution s) (hs_not_T : s ∉ T)
    (hinvT : ∀ x : G, x ∈ T → s * x * s⁻¹ = x⁻¹) :
    Nat.card (T ⊔ Subgroup.zpowers s : Subgroup G) = 2 * Nat.card T := by
  classical
  let Zs : Subgroup G := Subgroup.zpowers s
  have hs2 : s * s = 1 := by simpa [pow_two] using hsI.2
  have hsnorm : s ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hinvT x hx]
      exact T.inv_mem hx
    · intro hx
      have hss : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
      have hy := hinvT (s * x * s⁻¹) hx
      have hrecover : s * (s * x * s⁻¹) * s⁻¹ = x := by
        rw [hss]
        calc
          s * (s * x * s) * s = (s * s) * x * (s * s) := by group
          _ = x := by rw [hs2]; simp
      rw [hrecover] at hy
      rw [hy]
      exact T.inv_mem hx
  have hZs_le_norm : Zs ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.zpowers_le.mpr hsnorm
  have hs_order : orderOf s = 2 :=
    orderOf_eq_prime (x := s) (p := 2) hsI.2 hsI.1
  have hZs_card : Nat.card Zs = 2 := by
    simp [Zs, Nat.card_zpowers, hs_order]
  have hdisjoint : Disjoint T Zs := by
    rw [Subgroup.disjoint_def]
    intro x hxT hxZ
    by_contra hx1
    have hxOrder : orderOf x = 2 := by
      have hdiv : orderOf x ∣ 2 := by
        rw [← hZs_card]
        exact Subgroup.orderOf_dvd_natCard Zs hxZ
      exact ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
        (fun h => hx1 (orderOf_eq_one_iff.mp h))
    have hzxle : Subgroup.zpowers x ≤ Zs := Subgroup.zpowers_le.mpr hxZ
    have hzxcard : Nat.card (Subgroup.zpowers x) = 2 := by
      rw [Nat.card_zpowers, hxOrder]
    have hzxEq : Subgroup.zpowers x = Zs :=
      Subgroup.eq_of_le_of_card_ge hzxle (by rw [hZs_card, hzxcard])
    have hs_zx : s ∈ Subgroup.zpowers x := by
      rw [hzxEq]
      exact Subgroup.mem_zpowers s
    exact hs_not_T ((Subgroup.zpowers_le.mpr hxT) hs_zx)
  change Nat.card (T ⊔ Zs : Subgroup G) = 2 * Nat.card T
  rw [card_sup_eq_mul_of_disjoint_of_le_normalizer
    T Zs hZs_le_norm hdisjoint, hZs_card, Nat.mul_comm]

/-! ## The `PSL₂(K)` reflected join -/

/-- The reflected dihedral pair at the `PSL₂(K)` level: a cyclic torus `T`
of order `(q ± 1)/2` containing `t`, a reflection `s` inverting `T`, with
`C_{L₂(q)}(t) = T ⊔ ⟨s⟩`. -/
private theorem psl2_reflected_join_of_reflected
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    {t : PSL2 K} (ht : IsInvolution t)
    (U : Subgroup (PSL2 K)) (w : PSL2 K)
    (hUcyc : IsCyclic U) (hUeven : 2 ∣ Nat.card U)
    (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : PSL2 K, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hnormalizer : ∀ R : Subgroup (PSL2 K), R ≤ U → R ≠ ⊥ →
      Subgroup.normalizer (R : Set (PSL2 K)) = U ⊔ Subgroup.zpowers w) :
    ∃ T : Subgroup (PSL2 K), ∃ s : PSL2 K,
      IsCyclic T ∧ t ∈ T ∧ IsInvolution s ∧ s ∉ T ∧
      (∀ x : PSL2 K, x ∈ T → s * x * s⁻¹ = x⁻¹) ∧
      Subgroup.centralizer ({t} : Set (PSL2 K)) = T ⊔ Subgroup.zpowers s := by
  classical
  let : Fintype U := Fintype.ofFinite U
  obtain ⟨sU, hsUord⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 hUeven
  let s0 : PSL2 K := sU
  have hs0U : s0 ∈ U := sU.2
  have hs0ord : orderOf s0 = 2 := by
    have h := (orderOf_injective U.subtype U.subtype_injective sU).trans hsUord
    simpa [s0] using h
  have hs0I : IsInvolution s0 := by
    constructor
    · intro h
      have hord1 : orderOf s0 = 1 := by rw [h]; simp
      rw [hs0ord] at hord1
      norm_num at hord1
    · exact (orderOf_dvd_iff_pow_eq_one).mp (by rw [hs0ord])
  obtain ⟨g, hgt⟩ := psl2_involutions_conjugate_of_odd_prime_power
    K hK s0 t hs0I ht
  let T : Subgroup (PSL2 K) := U.map (MulAut.conj g).toMonoidHom
  have hTcyc : IsCyclic T := by
    let eU : U ≃* T := Subgroup.equivMapOfInjective U
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    exact (MulEquiv.isCyclic eU).mp hUcyc
  have htT : t ∈ T := by
    rw [← hgt]
    exact Subgroup.mem_map.mpr ⟨s0, hs0U, rfl⟩
  let s : PSL2 K := g * w * g⁻¹
  let e : PSL2 K ≃* PSL2 K := MulAut.conj g
  have hsI : IsInvolution s := by
    constructor
    · intro h
      apply hwU
      have hw1 : w = 1 := by
        calc
          w = g⁻¹ * (g * w * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by
            change g⁻¹ * s * g = g⁻¹ * 1 * g
            rw [h]
          _ = 1 := by simp
      rw [hw1]
      exact U.one_mem
    · calc
        (g * w * g⁻¹) ^ 2 = g * (w ^ 2) * g⁻¹ := by
          rw [pow_two]
          calc
            (g * w * g⁻¹) * (g * w * g⁻¹) =
                g * w * (g⁻¹ * g) * w * g⁻¹ := by group
            _ = g * w * 1 * w * g⁻¹ := by rw [inv_mul_cancel]
            _ = g * (w * w) * g⁻¹ := by group
            _ = g * (w ^ 2) * g⁻¹ := by rw [pow_two]
        _ = 1 := by
          have hw2 : w ^ 2 = 1 := by simpa [pow_two] using hwsq
          rw [hw2]
          simp
  have hs_not_T : s ∉ T := by
    intro hsT
    dsimp [T] at hsT
    rcases Subgroup.mem_map.mp hsT with ⟨u, hu, hgu⟩
    have hwU' : w ∈ U := by
      have huw : u = w := by
        have h' := congrArg (fun z : PSL2 K => g⁻¹ * z * g) hgu
        calc
          u = g⁻¹ * (s * g) := by simpa [MulAut.conj_apply, s, mul_assoc] using h'
          _ = g⁻¹ * ((g * w * g⁻¹) * g) := by rfl
          _ = w := by group
      simpa [huw] using hu
    exact hwU hwU'
  have hinvT : ∀ x : PSL2 K, x ∈ T → s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    dsimp [T] at hx
    rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
    have hwuinv : w * u * w⁻¹ = u⁻¹ := hwinv u hu
    calc
      (g * w * g⁻¹) * (g * u * g⁻¹) * (g * w * g⁻¹)⁻¹ =
          g * (w * u * w⁻¹) * g⁻¹ := by group
      _ = g * u⁻¹ * g⁻¹ := by rw [hwuinv]
      _ = (g * u * g⁻¹)⁻¹ := by group
  let R : Subgroup (PSL2 K) := Subgroup.zpowers s0
  have hRleU : R ≤ U := Subgroup.zpowers_le.mpr hs0U
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hs0R : s0 ∈ R := Subgroup.mem_zpowers s0
    have hs0bot : s0 ∈ (⊥ : Subgroup (PSL2 K)) := by simpa [hbot] using hs0R
    exact hs0I.1 (Subgroup.mem_bot.mp hs0bot)
  have hN0 : Subgroup.normalizer (R : Set (PSL2 K)) = U ⊔ Subgroup.zpowers w :=
    hnormalizer R hRleU hRne
  let Zt : Subgroup (PSL2 K) := Subgroup.zpowers t
  have hZt_map : Zt = R.map e.toMonoidHom := by
    have hmap : R.map e.toMonoidHom = Subgroup.zpowers (e s0) := by
      simp [R, e]
    rw [hmap]
    dsimp [Zt, e]
    rw [hgt]
  have hN0map : (Subgroup.normalizer (R : Set (PSL2 K))).map e.toMonoidHom =
      Subgroup.normalizer (Zt : Set (PSL2 K)) := by
    rw [hZt_map]
    exact Subgroup.map_equiv_normalizer_eq R e
  have hUsup_map : (U ⊔ Subgroup.zpowers w).map e.toMonoidHom =
      T ⊔ Subgroup.zpowers s := by
    simpa [T, s, e, Subgroup.map_sup, MonoidHom.map_zpowers, MulAut.conj_apply]
  have hNt : Subgroup.normalizer (Zt : Set (PSL2 K)) = T ⊔ Subgroup.zpowers s := by
    calc
      Subgroup.normalizer (Zt : Set (PSL2 K)) =
          (Subgroup.normalizer (R : Set (PSL2 K))).map e.toMonoidHom :=
        hN0map.symm
      _ = (U ⊔ Subgroup.zpowers w).map e.toMonoidHom := by rw [hN0]
      _ = T ⊔ Subgroup.zpowers s := hUsup_map
  have hC : Subgroup.centralizer ({t} : Set (PSL2 K)) = T ⊔ Subgroup.zpowers s := by
    apply le_antisymm
    · intro x hx
      rw [← hNt]
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      dsimp [Zt]
      rw [MonoidHom.map_zpowers]
      have hxt : (MulAut.conj x) t = t := by
        have hcomm : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx
        calc
          (MulAut.conj x) t = x * t * x⁻¹ := by simp [MulAut.conj_apply]
          _ = t * x * x⁻¹ := by rw [hcomm]
          _ = t := by group
      exact congrArg Subgroup.zpowers hxt
    · apply sup_le
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        rcases hTcyc with ⟨a, ha⟩
        rcases ha ⟨x, hx⟩ with ⟨n, hn⟩
        rcases ha ⟨t, htT⟩ with ⟨m, hm⟩
        have hab : (⟨x, hx⟩ : T) * (⟨t, htT⟩ : T) = (⟨t, htT⟩ : T) * (⟨x, hx⟩ : T) := by
          calc
            (⟨x, hx⟩ : T) * (⟨t, htT⟩ : T) = a ^ n * a ^ m := by simpa [hn, hm]
            _ = a ^ (n + m) := by rw [zpow_add]
            _ = a ^ (m + n) := by rw [add_comm]
            _ = a ^ m * a ^ n := by rw [zpow_add]
            _ = (⟨t, htT⟩ : T) * (⟨x, hx⟩ : T) := by simpa [← hm, ← hn]
        simpa using congrArg Subtype.val hab
      · rw [Subgroup.zpowers_le]
        rw [Subgroup.mem_centralizer_singleton_iff]
        have htinv : t⁻¹ = t := by
          have htt : t * t = 1 := by simpa [pow_two] using ht.2
          exact inv_eq_of_mul_eq_one_right htt
        calc
          s * t = t⁻¹ * s := by
            have hs := hinvT t htT
            exact mul_inv_eq_iff_eq_mul.mp hs
          _ = t * s := by rw [htinv]
  exact ⟨T, s, hTcyc, htT, hsI, hs_not_T, hinvT, hC⟩

/-- The reflected dihedral pair at the `PSL₂(K)` level (Huppert
split/nonsplit choice). -/
public theorem psl2_reflected_join
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    {t : PSL2 K} (ht : IsInvolution t) :
    ∃ T : Subgroup (PSL2 K), ∃ s : PSL2 K,
      IsCyclic T ∧ t ∈ T ∧ IsInvolution s ∧ s ∉ T ∧
      (∀ x : PSL2 K, x ∈ T → s * x * s⁻¹ = x⁻¹) ∧
      Subgroup.centralizer ({t} : Set (PSL2 K)) = T ⊔ Subgroup.zpowers s := by
  classical
  have hKfull : IsOddPrimePower (Nat.card K) := hK
  rcases hK with ⟨p, f, hp, hpOdd, hf, hcard⟩
  let : Fact p.Prime := ⟨hp⟩
  have hKcard : Nat.card K = p ^ f := hcard
  have hqodd : Odd (Nat.card K) := by
    rw [hcard]
    exact hpOdd.pow
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := gcd_sub_one_two_of_odd hqodd
  rcases Nat.even_or_odd ((Nat.card K - 1) / 2) with hsplit | hnonsplit
  · obtain ⟨U, w, hUc, hUcard, _hwN, hwU, hwsq, hwinv, _hDcard, hnormalizer⟩ :=
      huppert_II_8_3_split_torus_reflection_data (F := K) (p := p) (f := f) hKcard
    have hUcard' : Nat.card U = (Nat.card K - 1) / 2 := by
      simpa [hgcd] using hUcard
    have hUeven : 2 ∣ Nat.card U := by
      rw [hUcard']
      exact hsplit.two_dvd
    exact psl2_reflected_join_of_reflected hKfull ht U w hUc hUeven hwU hwsq hwinv
      hnormalizer
  · obtain ⟨U, w, hUc, hUcard, _hwN, hwU, hwsq, hwinv, _hDcard, hnormalizer⟩ :=
      huppert_II_8_4_nonsplit_torus_reflection_data (F := K) (p := p) (f := f) hKcard
    have hUcard' : Nat.card U = (Nat.card K + 1) / 2 := by
      simpa [hgcd] using hUcard
    have hEvenPlus : Even ((Nat.card K + 1) / 2) := by
      rcases hnonsplit with ⟨k, hk⟩
      use k + 1
      omega
    have hUeven : 2 ∣ Nat.card U := by
      rw [hUcard']
      exact hEvenPlus.two_dvd
    exact psl2_reflected_join_of_reflected hKfull ht U w hUc hUeven hwU hwsq hwinv
      hnormalizer

/-! ## The `S₀` image lies in the quotient torus -/

/-- Once the ambient Sylow lies in the component, the image of `S₀` in
`E/Z(E)` lies in the reflected torus of `SecondCasePSL2QuotientTorusCard`. -/
public theorem secondCase_psl2_S0_le_quotient_torus
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (torus : SecondCasePSL2QuotientTorusCard d K)
    (hSleE : (c.S : Subgroup G) ≤ d.E) :
    (c.S0.subgroupOf d.E).map (QuotientGroup.mk' (Subgroup.center d.E)) ≤ torus.T := by
  classical
  let Q : Type u := d.E ⧸ Subgroup.center d.E
  let q : d.E →* Q := QuotientGroup.mk' (Subgroup.center d.E)
  let tQ : Q := q ⟨c.t, d.t_mem_E⟩
  have htQ : IsInvolution tQ := by
    have htE : IsInvolution (⟨c.t, d.t_mem_E⟩ : d.E) := by
      constructor
      · intro h1
        exact c.t_involution.1 (congrArg Subtype.val h1)
      · apply Subtype.ext
        simpa [pow_two] using c.t_involution.2
    change IsInvolution (QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩)
    exact quotient_involution_of_involution (Subgroup.center d.E) d.center_odd htE
  let X : Subgroup Q := (c.S0.subgroupOf d.E).map q
  let e : Q ≃* PSL2 K := torus.modelEquiv.some
  let tP : PSL2 K := e tQ
  have htP : IsInvolution tP := by
    constructor
    · intro h1
      apply htQ.1
      exact (by
        simpa [tP] using congrArg (e.symm : PSL2 K → Q) h1)
    · simpa using congrArg e htQ.2
  obtain ⟨T0, s0, hT0cyc, htP_T0, hs0I, hs0_not_T0, hinvT0, hC0⟩ :=
    psl2_reflected_join (K := K) torus.primePower htP
  -- transport the reflected pair to `Q`
  let T0Q : Subgroup Q := T0.map e.symm.toMonoidHom
  let s0Q : Q := e.symm s0
  have hT0Qcyc : IsCyclic T0Q := by
    let eT : T0 ≃* T0Q := Subgroup.equivMapOfInjective T0
      e.symm.toMonoidHom e.symm.injective
    exact (MulEquiv.isCyclic eT).mp hT0cyc
  have htQ_T0Q : tQ ∈ T0Q := by
    have htP' : tP ∈ T0 := htP_T0
    exact Subgroup.mem_map.mpr ⟨tP, htP', by
      change e.symm.toMonoidHom tP = tQ
      simp [tP]⟩
  have hs0Q_I : IsInvolution s0Q := by
    constructor
    · intro h1
      apply hs0I.1
      have h : e.symm s0 = 1 := by simpa [s0Q] using h1
      have hs01 : s0 = 1 := by
        have h' := congrArg e h
        simpa using h'
      exact hs01
    · calc
        s0Q ^ 2 = e.symm.toMonoidHom (s0 ^ 2) := by
          simp [s0Q, map_pow]
        _ = 1 := by
          rw [hs0I.2]
          simp
  have hs0Q_not_T0Q : s0Q ∉ T0Q := by
    intro hsT
    rcases Subgroup.mem_map.mp hsT with ⟨y, hyT0, hyeq⟩
    have hy_eq : y = s0 := by
      apply e.symm.injective
      calc
        e.symm y = s0Q := hyeq
        _ = e.symm s0 := rfl
    exact hs0_not_T0 (by simpa [hy_eq] using hyT0)
  have hinvT0Q : ∀ x : Q, x ∈ T0Q → s0Q * x * s0Q⁻¹ = x⁻¹ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyT0, hx_eq⟩
    calc
      s0Q * x * s0Q⁻¹ = e.symm.toMonoidHom (s0 * y * s0⁻¹) := by
        rw [← hx_eq]
        dsimp [s0Q]
        rw [e.symm.map_mul, e.symm.map_mul, e.symm.map_inv]
      _ = e.symm.toMonoidHom (y⁻¹) := by rw [hinvT0 y hyT0]
      _ = (e.symm.toMonoidHom y)⁻¹ := by rw [e.symm.toMonoidHom.map_inv]
      _ = x⁻¹ := by rw [hx_eq]
  have hC0Q : Subgroup.centralizer ({tQ} : Set Q) = T0Q ⊔ Subgroup.zpowers s0Q := by
    have hCmap : (Subgroup.centralizer ({tP} : Set (PSL2 K))).map e.symm.toMonoidHom =
        Subgroup.centralizer ({tQ} : Set Q) := by
      ext y
      constructor
      · intro hy
        rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hcomm : x * tP = tP * x := Subgroup.mem_centralizer_singleton_iff.mp hx
        apply e.injective
        calc
          e (e.symm x * tQ) = x * tP := by simp [tP]
          _ = tP * x := hcomm
          _ = e (tQ * e.symm x) := by simp [tP]
      · intro hy
        have hx : e y ∈ Subgroup.centralizer ({tP} : Set (PSL2 K)) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hcomm : y * tQ = tQ * y := Subgroup.mem_centralizer_singleton_iff.mp hy
          dsimp [tP]
          rw [← map_mul, ← map_mul]
          exact congrArg e hcomm
        exact Subgroup.mem_map.mpr ⟨e y, hx, by
          change e.symm.toMonoidHom (e y) = y
          simp⟩
    calc
      Subgroup.centralizer ({tQ} : Set Q) =
          (Subgroup.centralizer ({tP} : Set (PSL2 K))).map
            e.symm.toMonoidHom := hCmap.symm
      _ = (T0 ⊔ Subgroup.zpowers s0).map e.symm.toMonoidHom := by rw [hC0]
      _ = T0Q ⊔ Subgroup.zpowers s0Q := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers]
        rfl
  -- the centralizer of `tQ` in `Q`
  have hXcent : X ≤ Subgroup.centralizer ({tQ} : Set Q) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyS0 : (y : G) ∈ c.S0 := Subgroup.mem_subgroupOf.mp hy
    have hyS : (y : G) ∈ (c.S : Subgroup G) := c.S0_le_S hyS0
    have hyC : (y : G) ∈ c.H := centralizerSetup_S_le_H c hyS
    have hyT : (y : G) ∈ Subgroup.centralizer ({c.t} : Set G) := by
      rw [← c.H_eq_centralizer]
      exact hyC
    have hcomm : (y : G) * c.t = c.t * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hyT
    have hcommE : y * (⟨c.t, d.t_mem_E⟩ : d.E) =
        (⟨c.t, d.t_mem_E⟩ : d.E) * y := Subtype.ext hcomm
    calc
      q y * q (⟨c.t, d.t_mem_E⟩ : d.E) = q (y * (⟨c.t, d.t_mem_E⟩ : d.E)) := by
        exact (map_mul q y (⟨c.t, d.t_mem_E⟩ : d.E)).symm
      _ = q ((⟨c.t, d.t_mem_E⟩ : d.E) * y) := by rw [hcommE]
      _ = q (⟨c.t, d.t_mem_E⟩ : d.E) * q y := by
        exact map_mul q (⟨c.t, d.t_mem_E⟩ : d.E) y
  -- X is cyclic and contains `tQ`
  have hS0leE : c.S0 ≤ d.E := c.S0_le_S.trans hSleE
  have hXcyc : IsCyclic X := by
    let S0E : Subgroup d.E := c.S0.subgroupOf d.E
    have hS0Ecyc : IsCyclic S0E :=
      (Subgroup.subgroupOfEquivOfLe hS0leE).isCyclic.mpr c.S0_cyclic
    let : IsCyclic S0E := hS0Ecyc
    change IsCyclic (S0E.map q)
    exact isCyclic_of_surjective
      (q.subgroupMap S0E) (q.subgroupMap_surjective S0E)
  have htQ_X : tQ ∈ X := by
    exact Subgroup.mem_map.mpr ⟨⟨c.t, d.t_mem_E⟩,
      Subgroup.mem_subgroupOf.mpr c.t_mem_S0, rfl⟩
  -- torus.T is a cyclic subgroup of the centralizer containing `tQ`
  have hT_cent : torus.T ≤ Subgroup.centralizer ({tQ} : Set Q) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases torus.T_cyclic with ⟨a, ha⟩
    rcases ha ⟨x, hx⟩ with ⟨n, hn⟩
    rcases ha ⟨tQ, torus.T_contains_t⟩ with ⟨m, hm⟩
    have hab : (⟨x, hx⟩ : torus.T) * (⟨tQ, torus.T_contains_t⟩ : torus.T) =
        (⟨tQ, torus.T_contains_t⟩ : torus.T) * (⟨x, hx⟩ : torus.T) := by
      calc
        (⟨x, hx⟩ : torus.T) * (⟨tQ, torus.T_contains_t⟩ : torus.T) =
            a ^ n * a ^ m := by simpa [hn, hm]
        _ = a ^ (n + m) := by rw [zpow_add]
        _ = a ^ (m + n) := by rw [add_comm]
        _ = a ^ m * a ^ n := by rw [zpow_add]
        _ = (⟨tQ, torus.T_contains_t⟩ : torus.T) * (⟨x, hx⟩ : torus.T) := by
          simpa [← hm, ← hn]
    simpa using congrArg Subtype.val hab
  have hT_le_T0Q : torus.T ≤ T0Q :=
    cyclic_subgroup_containing_involution_le_reflected_torus (G := Q) htQ T0Q s0Q
      hT0Qcyc htQ_T0Q hs0Q_I hs0Q_not_T0Q hinvT0Q hC0Q
      torus.T_cyclic hT_cent torus.T_contains_t
  -- the reflection inverts torus.T and lies outside it
  have hs0Q_invT : ∀ x : Q, x ∈ torus.T → s0Q * x * s0Q⁻¹ = x⁻¹ := by
    intro x hx
    exact hinvT0Q x (hT_le_T0Q hx)
  have hs0Q_not_T : s0Q ∉ torus.T := by
    intro hst
    exact hs0Q_not_T0Q (hT_le_T0Q hst)
  -- C(tQ) = torus.T ⊔ ⟨s0Q⟩ (equal cardinals)
  have hjoin_card : Nat.card (torus.T ⊔ Subgroup.zpowers s0Q : Subgroup Q) =
      2 * Nat.card torus.T :=
    join_card_of_inverting_reflection (G := Q) hs0Q_I hs0Q_not_T hs0Q_invT
  have hjoin_le_C : torus.T ⊔ Subgroup.zpowers s0Q ≤
      Subgroup.centralizer ({tQ} : Set Q) := by
    apply sup_le
    · exact hT_cent
    · rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_centralizer_singleton_iff]
      have htinv : tQ⁻¹ = tQ := by
        have htt : tQ * tQ = 1 := by simpa [pow_two] using htQ.2
        exact inv_eq_of_mul_eq_one_right htt
      calc
        s0Q * tQ = tQ⁻¹ * s0Q := by
          have hs := hinvT0Q tQ htQ_T0Q
          exact mul_inv_eq_iff_eq_mul.mp hs
        _ = tQ * s0Q := by rw [htinv]
  have hC_T : Subgroup.centralizer ({tQ} : Set Q) = torus.T ⊔ Subgroup.zpowers s0Q := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hjoin_le_C
    rw [hjoin_card, torus.T_centralizer_card]
  -- the cyclic containment with the pair (torus.T, s0Q)
  have hX_le_T : X ≤ torus.T :=
    cyclic_subgroup_containing_involution_le_reflected_torus (G := Q) htQ torus.T s0Q
      torus.T_cyclic torus.T_contains_t hs0Q_I hs0Q_not_T hs0Q_invT hC_T
      hXcyc hXcent htQ_X
  exact hX_le_T

end CFSG.GorensteinWalter
