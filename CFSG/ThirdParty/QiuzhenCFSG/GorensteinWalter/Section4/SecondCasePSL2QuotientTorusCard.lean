module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralOddRotationCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_3_split
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The quotient reflected torus with its exact cardinality

The existing `secondCase_reflection_psl2_torus(_fixedSylow)` endpoints and
the quotient package `secondCase_quotient_reflected_torus_data` omit
`Nat.card T` (and even `t ∈ T`), so the cardinal orientation of the torus
cannot be recovered from their existential results.  This module builds a
separate, richer package directly from the Huppert split/nonsplit torus data
(`huppert_II_8_3_split_torus_reflection_data` /
`huppert_II_8_4_nonsplit_torus_reflection_data`): a cyclic torus
`T ≤ E/Z(E)` containing the quotient involution
`q ⟨t, _⟩` — hence of *even* order — with the exact cardinal
`Nat.card T = (q ± 1)/2`, and with the maximality clause that every odd
cyclic subgroup of `E/Z(E)` centralized by `q t` lies in `T`.

This is the quotient-level replacement needed by equation (9): the even
half `k = |T|`, the injection of `K₀` into `T`, the bound `2p ≤ k` from
`p | |K₀|`, and `q ≥ 7` — all without `Z(E) = 1`.
-/

noncomputable section

open BenderSuzuki
open BenderSuzuki.External

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

private lemma odd_card_field {K : Type u} [Field K] [Finite K]
    (hodd : IsOddPrimePower (Nat.card K)) : Odd (Nat.card K) := by
  rcases hodd with ⟨p, n, hp, hpOdd, hn, hcard⟩
  rw [hcard]
  exact hpOdd.pow

public lemma gcd_sub_one_two_of_odd {q : ℕ} (hq : Odd q) :
    Nat.gcd (q - 1) 2 = 2 := by
  have h2 : 2 ∣ q - 1 := by
    rcases hq with ⟨k, hk⟩
    use k
    omega
  exact Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
    (Nat.dvd_gcd h2 (dvd_refl 2))

/-- The quotient image of an involution is an involution when the kernel has
odd order. -/
public theorem quotient_involution_of_involution
    {Q : Type u} [Group Q] [Finite Q]
    (N : Subgroup Q) [N.Normal] (hNodd : Odd (Nat.card N))
    {x : Q} (hx : IsInvolution x) :
    IsInvolution (QuotientGroup.mk' N x) := by
  constructor
  · intro hqx
    have hxN : x ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) x).mp hqx
    let xN : N := ⟨x, hxN⟩
    have hxNI : IsInvolution xN := by
      constructor
      · intro hone
        exact hx.1 (congrArg Subtype.val hone)
      · exact Subtype.ext hx.2
    have hxNOrder : orderOf xN = 2 :=
      orderOf_eq_prime hxNI.2 hxNI.1
    have htwo : 2 ∣ Nat.card N := by
      rw [← hxNOrder]
      exact orderOf_dvd_natCard xN
    exact hNodd.not_two_dvd_nat htwo
  · simpa using congrArg (QuotientGroup.mk' N) hx.2

/-- An odd subgroup centralized by the torus involution lies in the torus,
for a cyclic torus with dihedral normalizer (reflection `w` inverting `U`). -/
private theorem odd_centralizer_le_torus_of_inverting_join_fixed
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (s w : G)
    (hsU : s ∈ U) (hsI : IsInvolution s)
    (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hnormalizer : ∀ R : Subgroup G, R ≤ U → R ≠ ⊥ →
      Subgroup.normalizer (R : Set G) = U ⊔ Subgroup.zpowers w)
    (X : Subgroup G) (hXodd : ∀ x : G, x ∈ X → Odd (orderOf x))
    (hXcent : X ≤ Subgroup.centralizer ({s} : Set G)) :
    X ≤ U := by
  intro x hx
  have hxcent : x ∈ Subgroup.centralizer ({s} : Set G) := hXcent hx
  let R : Subgroup G := Subgroup.zpowers s
  have hRleU : R ≤ U := Subgroup.zpowers_le.mpr hsU
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hsR : s ∈ R := Subgroup.mem_zpowers s
    have hsbot : s ∈ (⊥ : Subgroup G) := by simpa [hbot] using hsR
    exact hsI.1 (Subgroup.mem_bot.mp hsbot)
  have hxcentR : x ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hxcent ⊢
    intro y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    have hcs : Commute x s := by
      have h : s * x = x * s := hxcent s (by simp)
      exact h.symm
    exact (hcs.zpow_right n).symm
  have hxN : x ∈ Subgroup.normalizer (R : Set G) :=
    (Subgroup.centralizer_le_normalizer (R : Set G)) hxcentR
  have hN : Subgroup.normalizer (R : Set G) = U ⊔ Subgroup.zpowers w :=
    hnormalizer R hRleU hRne
  have hxUw : x ∈ U ⊔ Subgroup.zpowers w := by
    rw [← hN]
    exact hxN
  rcases (mem_sup_zpowers_of_involution_inverts hwU hwsq hwinv).mp hxUw with
    ⟨u, hu, hx_or⟩
  rcases hx_or with hxu | hxuw
  · rw [hxu]
    exact hu
  · exfalso
    have hxodd : Odd (orderOf x) := hXodd x hx
    have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hwsq
    have hwuw : w * u * w = u⁻¹ := by
      calc
        w * u * w = (w * u * w⁻¹) * w * w := by
          rw [hw_inv]
          simp [mul_assoc, hwsq]
        _ = u⁻¹ * w * w := by rw [hwinv u hu]
        _ = u⁻¹ := by rw [mul_assoc, hwsq, mul_one]
    have hx2 : (u * w) ^ 2 = 1 := by
      rw [pow_two]
      calc
        (u * w) * (u * w) = u * (w * u * w) := by group
        _ = u * u⁻¹ := by rw [hwuw]
        _ = 1 := by simp
    have hord2 : orderOf (u * w) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [hxuw] using hx2)
    have huw_ne : u * w ≠ 1 := by
      intro h1
      apply hwU
      have hw_eq : w = u⁻¹ := by
        calc
          w = u⁻¹ * (u * w) := by group
          _ = u⁻¹ * 1 := by rw [h1]
          _ = u⁻¹ := by simp
      simpa [hw_eq] using U.inv_mem hu
    have hord_eq : orderOf (u * w) = 2 :=
      orderOf_eq_prime (by simpa [hxuw] using hx2) huw_ne
    have h2dvd : 2 ∣ orderOf x := by
      rw [hxuw, hord_eq]
    exact hxodd.not_two_dvd_nat h2dvd

/-- The centralizer of the torus involution is the reflected join, of order
`2 · |T|`: the normalizer of `⟨t⟩` is the dihedral join `T ⊔ ⟨s⟩` (the
conjugate of the Huppert normalizer data), the centralizer of the
involution `t` equals that normalizer, and the join has twice the order of
the torus. -/
private theorem torus_centralizer_card_of_reflected
    {K : Type u} [Field K] [Finite K]
    {t : PSL2 K} (ht : IsInvolution t)
    (U : Subgroup (PSL2 K)) (w : PSL2 K)
    (hUcyc : IsCyclic U) (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : PSL2 K, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hnormalizer : ∀ R : Subgroup (PSL2 K), R ≤ U → R ≠ ⊥ →
      Subgroup.normalizer (R : Set (PSL2 K)) = U ⊔ Subgroup.zpowers w)
    (hDcard : Nat.card (U ⊔ Subgroup.zpowers w : Subgroup (PSL2 K)) =
      2 * Nat.card U)
    {s0 : PSL2 K} (hs0U : s0 ∈ U) (hs0I : IsInvolution s0)
    {g : PSL2 K} (hgt : g * s0 * g⁻¹ = t)
    (T : Subgroup (PSL2 K)) (hT : T = U.map (MulAut.conj g).toMonoidHom)
    (hTcyc : IsCyclic T) (htT : t ∈ T) :
    Nat.card (Subgroup.centralizer ({t} : Set (PSL2 K))) = 2 * Nat.card T := by
  classical
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
    rw [hT] at hsT
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
    rw [hT] at hx
    rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
    have hwuinv : w * u * w⁻¹ = u⁻¹ := hwinv u hu
    calc
      (g * w * g⁻¹) * (g * u * g⁻¹) * (g * w * g⁻¹)⁻¹ =
          g * (w * u * w⁻¹) * g⁻¹ := by group
      _ = g * u⁻¹ * g⁻¹ := by rw [hwuinv]
      _ = (g * u * g⁻¹)⁻¹ := by group
  -- the normalizer of `⟨t⟩` is the reflected join
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
    simpa [hT, s, e, Subgroup.map_sup, MonoidHom.map_zpowers, MulAut.conj_apply]
  have hNt : Subgroup.normalizer (Zt : Set (PSL2 K)) = T ⊔ Subgroup.zpowers s := by
    calc
      Subgroup.normalizer (Zt : Set (PSL2 K)) =
          (Subgroup.normalizer (R : Set (PSL2 K))).map e.toMonoidHom :=
        hN0map.symm
      _ = (U ⊔ Subgroup.zpowers w).map e.toMonoidHom := by rw [hN0]
      _ = T ⊔ Subgroup.zpowers s := hUsup_map
  -- the centralizer of the involution equals the join
  have hTleC : T ≤ Subgroup.centralizer ({t} : Set (PSL2 K)) := by
    rcases hTcyc with ⟨a, ha⟩
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
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
  have hsC : s ∈ Subgroup.centralizer ({t} : Set (PSL2 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have htinv : t⁻¹ = t := by
      have htt : t * t = 1 := by simpa [pow_two] using ht.2
      exact inv_eq_of_mul_eq_one_right htt
    calc
      s * t = t⁻¹ * s := by
        have hs := hinvT t htT
        -- s * t * s⁻¹ = t⁻¹ ⟹ s * t = t⁻¹ * s
        exact mul_inv_eq_iff_eq_mul.mp hs
      _ = t * s := by rw [htinv]
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
    · exact sup_le hTleC (Subgroup.zpowers_le.mpr hsC)
  -- the join has twice the torus order
  have hD : Nat.card (T ⊔ Subgroup.zpowers s : Subgroup (PSL2 K)) = 2 * Nat.card T := by
    have hmapcard : Nat.card ((U ⊔ Subgroup.zpowers w).map e.toMonoidHom) =
        Nat.card (U ⊔ Subgroup.zpowers w : Subgroup (PSL2 K)) :=
      Subgroup.card_map_of_injective (K := U ⊔ Subgroup.zpowers w)
        (f := e.toMonoidHom) e.injective
    have hUcardT : Nat.card U = Nat.card T := by
      rw [hT]
      exact (Subgroup.card_map_of_injective (K := U)
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).symm
    calc
      Nat.card (T ⊔ Subgroup.zpowers s : Subgroup (PSL2 K)) =
          Nat.card ((U ⊔ Subgroup.zpowers w).map e.toMonoidHom) := by
        rw [hUsup_map]
      _ = Nat.card (U ⊔ Subgroup.zpowers w : Subgroup (PSL2 K)) := hmapcard
      _ = 2 * Nat.card U := hDcard
      _ = 2 * Nat.card T := by rw [hUcardT]
  rwa [← hC] at hD

/-- Conjugating an element of the centralizer of a conjugate singleton into
the centralizer of the original singleton. -/
private theorem centralizer_conj_mem_fixed
    {G : Type u} [Group G] (g t x : G)
    (hx : x ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set G)) :
    g⁻¹ * x * g ∈ Subgroup.centralizer ({t} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  have h' : g⁻¹ * (x * (g * t * g⁻¹)) * g =
      g⁻¹ * ((g * t * g⁻¹) * x) * g :=
    congrArg (fun z : G => g⁻¹ * z * g) hx
  simpa [mul_assoc] using h'

/-- The quotient reflected torus with exact cardinality: a cyclic torus
`T ≤ E/Z(E)` containing the quotient involution `q ⟨t, _⟩`, of even order
`(q ± 1)/2`, whose maximality clause controls every odd cyclic subgroup
centralized by `q t`. -/
public structure SecondCasePSL2QuotientTorusCard
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {w : SecondCaseWitness c}
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K] where
  primePower : IsOddPrimePower (Nat.card K)
  modelEquiv : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K)
  T : Subgroup (d.E ⧸ Subgroup.center d.E)
  T_cyclic : IsCyclic T
  T_contains_t :
    QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩ ∈ T
  /-- `T` contains the quotient involution, so its order is even. -/
  T_even : Even (Nat.card T)
  /-- The exact cardinal orientation: `|T| = (q ± 1)/2`. -/
  T_card : Nat.card T = (Nat.card K - 1) / 2 ∨
    Nat.card T = (Nat.card K + 1) / 2
  /-- Every odd cyclic subgroup of `E/Z(E)` centralized by the image of
  `t` lies in `T`. -/
  T_odd_centralized_le : ∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
    (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X → Odd (orderOf x)) →
      X ≤ Subgroup.centralizer
        ({QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩} :
          Set (d.E ⧸ Subgroup.center d.E)) → X ≤ T
  /-- The centralizer of the quotient involution is the reflected join, of
  order `2 · |T|` (the source's `|C_{L₂(q)}(t)| = 2k`).  This is the
  `|M : H ∩ M| = q · k'` input of `SecondCasePSL2CentralizerIndex`. -/
  T_centralizer_card :
    Nat.card (Subgroup.centralizer
      ({QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩} :
        Set (d.E ⧸ Subgroup.center d.E))) = 2 * Nat.card T
  /-- The selected torus has the normalizer cardinality required by the
  order-`p` orbit count. -/
  T_normalizer_card :
    Nat.card (Subgroup.normalizer (T : Set (d.E ⧸ Subgroup.center d.E))) =
      2 * Nat.card T

private theorem normalizer_card_of_map_equiv
    {G N : Type u} [Group G] [Group N] [Finite G] [Finite N]
    (U : Subgroup G) (e : G ≃* N)
    (h : Nat.card (Subgroup.normalizer (U : Set G)) = 2 * Nat.card U) :
    Nat.card (Subgroup.normalizer
      ((U.map e.toMonoidHom : Subgroup N) : Set N)) =
      2 * Nat.card (U.map e.toMonoidHom) := by
  have hmap := Subgroup.map_equiv_normalizer_eq U e
  have hc := Subgroup.card_map_of_injective
    (K := Subgroup.normalizer (U : Set G)) (f := e.toMonoidHom) e.injective
  change Nat.card (Subgroup.normalizer
      ((U.map e.toMonoidHom : Subgroup N) : Set N)) =
    2 * Nat.card (U.map e.toMonoidHom)
  rw [← hmap, hc, h]
  exact congrArg (fun n => 2 * n)
    (Subgroup.card_map_of_injective
      (K := U) (f := e.toMonoidHom) e.injective).symm

/-- The construction: choose the Huppert split torus when `(q - 1)/2` is
even and the nonsplit torus otherwise, take its order-two element, conjugate
it to the image of `t`, and transport the resulting torus back through the
model equivalence to `E/Z(E)`.  The torus contains the image of `t`, so its
order is the even half `(q ± 1)/2`; the odd-centralized maximality is the
dihedral-normalizer argument of Huppert II.8.3/II.8.4. -/
public theorem secondCase_psl2_quotient_torus_card
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K)) :
    Nonempty (SecondCasePSL2QuotientTorusCard d K) := by
  classical
  let Q : Type u := d.E ⧸ Subgroup.center d.E
  let q : d.E →* Q := QuotientGroup.mk' (Subgroup.center d.E)
  let tQ : Q := q ⟨c.t, d.t_mem_E⟩
  have hqodd : Odd (Nat.card K) := odd_card_field hK
  have htQ : IsInvolution tQ := by
    have htE : IsInvolution (⟨c.t, d.t_mem_E⟩ : d.E) := by
      constructor
      · intro h1
        exact c.t_involution.1 (congrArg Subtype.val h1)
      · apply Subtype.ext
        simpa [pow_two] using c.t_involution.2
    change IsInvolution (QuotientGroup.mk' (Subgroup.center d.E)
      ⟨c.t, d.t_mem_E⟩)
    exact quotient_involution_of_involution (Subgroup.center d.E)
      d.center_odd htE
  let tP : PSL2 K := e.some tQ
  have htP : IsInvolution tP := by
    constructor
    · intro h1
      apply htQ.1
      exact (by
        simpa [tP] using congrArg (e.some.symm : PSL2 K → Q) h1)
    · simpa using congrArg e.some htQ.2
  let hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 :=
    gcd_sub_one_two_of_odd hqodd
  rcases hK with ⟨p, f, hp, hpOdd, hf, hcard⟩
  let : Fact p.Prime := ⟨hp⟩
  have hKcard : Nat.card K = p ^ f := hcard
  let hKfull : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hpOdd, hf, hcard⟩
  rcases Nat.even_or_odd ((Nat.card K - 1) / 2) with hsplit | hnonsplit
  · -- the split torus has even order
    obtain ⟨U, w, hUc, hUcard, _hwN, hwU, hwsq, hwinv, hDcard, hnormalizer⟩ :=
      huppert_II_8_3_split_torus_reflection_data (F := K) (p := p) (f := f)
        hKcard
    have hUcard' : Nat.card U = (Nat.card K - 1) / 2 := by
      simpa [hgcd] using hUcard
    have hUeven : 2 ∣ Nat.card U := by
      rw [hUcard']
      exact hsplit.two_dvd
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
      K hKfull s0 tP hs0I htP
    let T0 : Subgroup (PSL2 K) := U.map (MulAut.conj g).toMonoidHom
    have hT0cyc : IsCyclic T0 := by
      let eU : U ≃* T0 := Subgroup.equivMapOfInjective U
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      exact (MulEquiv.isCyclic eU).mp hUc
    have hT0card : Nat.card T0 = (Nat.card K - 1) / 2 := by
      simpa [T0] using (Subgroup.card_map_of_injective
        (K := U) (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective).trans hUcard'
    have hUne : U ≠ ⊥ := by
      intro hUbot
      have hs0bot : s0 ∈ (⊥ : Subgroup (PSL2 K)) := by
        simpa [hUbot] using hs0U
      exact hs0I.1 (Subgroup.mem_bot.mp hs0bot)
    have hUnormcard : Nat.card (Subgroup.normalizer (U : Set (PSL2 K))) =
        2 * Nat.card U := by
      rw [hnormalizer U le_rfl hUne]
      exact hDcard
    have hT0normcard : Nat.card
        (Subgroup.normalizer (T0 : Set (PSL2 K))) = 2 * Nat.card T0 := by
      simpa [T0] using normalizer_card_of_map_equiv U (MulAut.conj g) hUnormcard
    have htP_T0 : tP ∈ T0 := by
      rw [← hgt]
      exact Subgroup.mem_map.mpr ⟨s0, hs0U, rfl⟩
    have hT0even : Even (Nat.card T0) := by
      rw [hT0card]
      exact hsplit
    have hT0contain : ∀ X : Subgroup (PSL2 K),
        (∀ x : PSL2 K, x ∈ X → Odd (orderOf x)) →
          X ≤ Subgroup.centralizer ({tP} : Set (PSL2 K)) → X ≤ T0 := by
      intro X hXodd hXcent x hx
      let X0 : Subgroup (PSL2 K) := X.map (MulAut.conj g⁻¹).toMonoidHom
      have hX0odd : ∀ y : PSL2 K, y ∈ X0 → Odd (orderOf y) := by
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨x0, hx0, rfl⟩
        have hord : orderOf ((MulAut.conj g⁻¹) x0) = orderOf x0 :=
          (MulAut.conj g⁻¹).orderOf_eq x0
        change Odd (orderOf ((MulAut.conj g⁻¹) x0))
        rw [hord]
        exact hXodd x0 hx0
      have hX0cent : X0 ≤ Subgroup.centralizer ({s0} : Set (PSL2 K)) := by
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨x0, hx0, rfl⟩
        have hxcent : x0 ∈ Subgroup.centralizer ({tP} : Set (PSL2 K)) :=
          hXcent hx0
        have hxcent' : x0 ∈ Subgroup.centralizer
            ({g * s0 * g⁻¹} : Set (PSL2 K)) := by
          simpa [hgt] using hxcent
        have hback := centralizer_conj_mem_fixed
          (G := PSL2 K) g s0 x0 hxcent'
        simpa [MulAut.conj_apply] using hback
      have hX0U : X0 ≤ U := odd_centralizer_le_torus_of_inverting_join_fixed
        (G := PSL2 K) U s0 w hs0U hs0I hwU hwsq hwinv hnormalizer
        X0 hX0odd hX0cent
      have hy : g⁻¹ * x * g ∈ X0 :=
        Subgroup.mem_map.mpr ⟨x, hx, by simp⟩
      have hyU : g⁻¹ * x * g ∈ U := hX0U hy
      exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hyU, by
        simp [mul_assoc]⟩
    have hCcard : Nat.card (Subgroup.centralizer ({tP} : Set (PSL2 K))) =
        2 * Nat.card T0 :=
      torus_centralizer_card_of_reflected (K := K) htP U w hUc hwU hwsq hwinv
        hnormalizer hDcard hs0U hs0I hgt T0 rfl hT0cyc htP_T0
    -- transport through the model equivalence back to `E/Z(E)`
    let T : Subgroup Q := T0.map e.some.symm.toMonoidHom
    have hTcyc : IsCyclic T := by
      let eT : T0 ≃* T := Subgroup.equivMapOfInjective T0
        e.some.symm.toMonoidHom e.some.symm.injective
      exact (MulEquiv.isCyclic eT).mp hT0cyc
    have htQ_T : tQ ∈ T := by
      have htP' : tP ∈ T0 := htP_T0
      exact Subgroup.mem_map.mpr ⟨tP, htP', by
        change e.some.symm.toMonoidHom tP = tQ
        simp [tP]⟩
    have hTcard : Nat.card T = (Nat.card K - 1) / 2 := by
      simpa [T] using (Subgroup.card_map_of_injective
        (K := T0) (f := e.some.symm.toMonoidHom)
        e.some.symm.injective).trans hT0card
    have hTeven : Even (Nat.card T) := by
      rw [hTcard]
      exact hsplit
    have hTcontain : ∀ X : Subgroup Q,
        (∀ x : Q, x ∈ X → Odd (orderOf x)) →
          X ≤ Subgroup.centralizer ({tQ} : Set Q) → X ≤ T := by
      intro X hXodd hXcent
      have hX0 : ∀ y : PSL2 K, y ∈ X.map e.some.toMonoidHom →
          Odd (orderOf y) := by
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨x0, hx0, rfl⟩
        have hord : orderOf (e.some x0) = orderOf x0 := e.some.orderOf_eq x0
        change Odd (orderOf (e.some x0))
        rw [hord]
        exact hXodd x0 hx0
      have hX0cent : X.map e.some.toMonoidHom ≤
          Subgroup.centralizer ({tP} : Set (PSL2 K)) := by
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨x0, hx0, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hxcent : x0 ∈ Subgroup.centralizer ({tQ} : Set Q) := hXcent hx0
        have hcomm : x0 * tQ = tQ * x0 :=
          Subgroup.mem_centralizer_singleton_iff.mp hxcent
        have hP : e.some x0 * tP = tP * e.some x0 := by
          calc
            e.some x0 * tP = e.some x0 * e.some tQ := rfl
            _ = e.some (x0 * tQ) := by rw [map_mul]
            _ = e.some (tQ * x0) := by rw [hcomm]
            _ = e.some tQ * e.some x0 := by rw [map_mul]
            _ = tP * e.some x0 := rfl
        exact hP
      have hX0T0 : X.map e.some.toMonoidHom ≤ T0 :=
        hT0contain (X.map e.some.toMonoidHom) hX0 hX0cent
      intro x hx
      have hxP : e.some x ∈ T0 := hX0T0 (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      exact Subgroup.mem_map.mpr ⟨e.some x, hxP, by
        change e.some.symm.toMonoidHom (e.some x) = x
        simp⟩
    have hCcardQ : Nat.card (Subgroup.centralizer ({tQ} : Set Q)) =
        2 * Nat.card T := by
      have hCmap : (Subgroup.centralizer ({tP} : Set (PSL2 K))).map
            e.some.symm.toMonoidHom = Subgroup.centralizer ({tQ} : Set Q) := by
        ext y
        constructor
        · intro hy
          rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hcomm : x * tP = tP * x :=
            Subgroup.mem_centralizer_singleton_iff.mp hx
          apply e.some.injective
          calc
            e.some (e.some.symm x * tQ) = x * tP := by simp [tP]
            _ = tP * x := hcomm
            _ = e.some (tQ * e.some.symm x) := by simp [tP]
        · intro hy
          have hx : e.some y ∈ Subgroup.centralizer ({tP} : Set (PSL2 K)) := by
            rw [Subgroup.mem_centralizer_singleton_iff]
            have hcomm : y * tQ = tQ * y :=
              Subgroup.mem_centralizer_singleton_iff.mp hy
            dsimp [tP]
            rw [← map_mul, ← map_mul]
            exact congrArg e.some hcomm
          exact Subgroup.mem_map.mpr ⟨e.some y, hx, by
            change e.some.symm.toMonoidHom (e.some y) = y
            simp⟩
      have hCcardT0 : Nat.card (Subgroup.centralizer ({tP} : Set (PSL2 K))) =
          Nat.card (Subgroup.centralizer ({tQ} : Set Q)) := by
        rw [← hCmap]
        exact (Subgroup.card_map_of_injective
          (K := Subgroup.centralizer ({tP} : Set (PSL2 K)))
          (f := e.some.symm.toMonoidHom) e.some.symm.injective).symm
      have hTeq : Nat.card T = Nat.card T0 := by
        rw [hTcard, hT0card]
      calc
        Nat.card (Subgroup.centralizer ({tQ} : Set Q)) =
            Nat.card (Subgroup.centralizer ({tP} : Set (PSL2 K))) :=
          hCcardT0.symm
        _ = 2 * Nat.card T0 := hCcard
        _ = 2 * Nat.card T := by rw [hTeq]
    have hTnormcard : Nat.card
        (Subgroup.normalizer (T : Set Q)) = 2 * Nat.card T := by
      simpa [T] using normalizer_card_of_map_equiv T0 e.some.symm hT0normcard
    exact ⟨⟨hKfull, e, T, hTcyc, htQ_T, hTeven,
      Or.inl hTcard, hTcontain, hCcardQ, hTnormcard⟩⟩
  · -- the nonsplit torus has even order
    obtain ⟨S0, w, hSc, hScard, _hwN, hwS, hwsq, hwinv, hDcard, hnormalizer⟩ :=
      huppert_II_8_4_nonsplit_torus_reflection_data (F := K) (p := p) (f := f)
        hKcard
    have hScard' : Nat.card S0 = (Nat.card K + 1) / 2 := by
      simpa [hgcd] using hScard
    have hSeven : Even ((Nat.card K + 1) / 2) := by
      rcases hnonsplit with ⟨k, hk⟩
      use k + 1
      omega
    have hUeven : 2 ∣ Nat.card S0 := by
      rw [hScard']
      exact hSeven.two_dvd
    let : Fintype S0 := Fintype.ofFinite S0
    obtain ⟨sU, hsUord⟩ := exists_prime_orderOf_dvd_card' (G := S0) 2 hUeven
    let s0 : PSL2 K := sU
    have hs0U : s0 ∈ S0 := sU.2
    have hs0ord : orderOf s0 = 2 := by
      have h := (orderOf_injective S0.subtype S0.subtype_injective sU).trans hsUord
      simpa [s0] using h
    have hs0I : IsInvolution s0 := by
      constructor
      · intro h
        have hord1 : orderOf s0 = 1 := by rw [h]; simp
        rw [hs0ord] at hord1
        norm_num at hord1
      · exact (orderOf_dvd_iff_pow_eq_one).mp (by rw [hs0ord])
    obtain ⟨g, hgt⟩ := psl2_involutions_conjugate_of_odd_prime_power
      K hKfull s0 tP hs0I htP
    let T0 : Subgroup (PSL2 K) := S0.map (MulAut.conj g).toMonoidHom
    have hT0cyc : IsCyclic T0 := by
      let eU : S0 ≃* T0 := Subgroup.equivMapOfInjective S0
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      exact (MulEquiv.isCyclic eU).mp hSc
    have hT0card : Nat.card T0 = (Nat.card K + 1) / 2 := by
      simpa [T0] using (Subgroup.card_map_of_injective
        (K := S0) (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective).trans hScard'
    have hS0ne : S0 ≠ ⊥ := by
      intro hS0bot
      have hs0bot : s0 ∈ (⊥ : Subgroup (PSL2 K)) := by
        simpa [hS0bot] using hs0U
      exact hs0I.1 (Subgroup.mem_bot.mp hs0bot)
    have hS0normcard : Nat.card
        (Subgroup.normalizer (S0 : Set (PSL2 K))) =
        2 * Nat.card S0 := by
      rw [hnormalizer S0 le_rfl hS0ne]
      exact hDcard
    have hT0normcard : Nat.card
        (Subgroup.normalizer (T0 : Set (PSL2 K))) = 2 * Nat.card T0 := by
      simpa [T0] using normalizer_card_of_map_equiv S0 (MulAut.conj g) hS0normcard
    have htP_T0 : tP ∈ T0 := by
      rw [← hgt]
      exact Subgroup.mem_map.mpr ⟨s0, hs0U, rfl⟩
    have hT0even : Even (Nat.card T0) := by
      rw [hT0card]
      exact hSeven
    have hT0contain : ∀ X : Subgroup (PSL2 K),
        (∀ x : PSL2 K, x ∈ X → Odd (orderOf x)) →
          X ≤ Subgroup.centralizer ({tP} : Set (PSL2 K)) → X ≤ T0 := by
      intro X hXodd hXcent x hx
      let X0 : Subgroup (PSL2 K) := X.map (MulAut.conj g⁻¹).toMonoidHom
      have hX0odd : ∀ y : PSL2 K, y ∈ X0 → Odd (orderOf y) := by
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨x0, hx0, rfl⟩
        have hord : orderOf ((MulAut.conj g⁻¹) x0) = orderOf x0 :=
          (MulAut.conj g⁻¹).orderOf_eq x0
        change Odd (orderOf ((MulAut.conj g⁻¹) x0))
        rw [hord]
        exact hXodd x0 hx0
      have hX0cent : X0 ≤ Subgroup.centralizer ({s0} : Set (PSL2 K)) := by
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨x0, hx0, rfl⟩
        have hxcent : x0 ∈ Subgroup.centralizer ({tP} : Set (PSL2 K)) :=
          hXcent hx0
        have hxcent' : x0 ∈ Subgroup.centralizer
            ({g * s0 * g⁻¹} : Set (PSL2 K)) := by
          simpa [hgt] using hxcent
        have hback := centralizer_conj_mem_fixed
          (G := PSL2 K) g s0 x0 hxcent'
        simpa [MulAut.conj_apply] using hback
      have hX0U : X0 ≤ S0 := odd_centralizer_le_torus_of_inverting_join_fixed
        (G := PSL2 K) S0 s0 w hs0U hs0I hwS hwsq hwinv hnormalizer
        X0 hX0odd hX0cent
      have hy : g⁻¹ * x * g ∈ X0 :=
        Subgroup.mem_map.mpr ⟨x, hx, by simp⟩
      have hyU : g⁻¹ * x * g ∈ S0 := hX0U hy
      exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hyU, by
        simp [mul_assoc]⟩
    have hCcard : Nat.card (Subgroup.centralizer ({tP} : Set (PSL2 K))) =
        2 * Nat.card T0 :=
      torus_centralizer_card_of_reflected (K := K) htP S0 w hSc hwS hwsq hwinv
        hnormalizer hDcard hs0U hs0I hgt T0 rfl hT0cyc htP_T0
    -- transport through the model equivalence back to `E/Z(E)`
    let T : Subgroup Q := T0.map e.some.symm.toMonoidHom
    have hTcyc : IsCyclic T := by
      let eT : T0 ≃* T := Subgroup.equivMapOfInjective T0
        e.some.symm.toMonoidHom e.some.symm.injective
      exact (MulEquiv.isCyclic eT).mp hT0cyc
    have htQ_T : tQ ∈ T := by
      have htP' : tP ∈ T0 := htP_T0
      exact Subgroup.mem_map.mpr ⟨tP, htP', by
        change e.some.symm.toMonoidHom tP = tQ
        simp [tP]⟩
    have hTcard : Nat.card T = (Nat.card K + 1) / 2 := by
      simpa [T] using (Subgroup.card_map_of_injective
        (K := T0) (f := e.some.symm.toMonoidHom)
        e.some.symm.injective).trans hT0card
    have hTeven : Even (Nat.card T) := by
      rw [hTcard]
      exact hSeven
    have hTcontain : ∀ X : Subgroup Q,
        (∀ x : Q, x ∈ X → Odd (orderOf x)) →
          X ≤ Subgroup.centralizer ({tQ} : Set Q) → X ≤ T := by
      intro X hXodd hXcent
      have hX0 : ∀ y : PSL2 K, y ∈ X.map e.some.toMonoidHom →
          Odd (orderOf y) := by
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨x0, hx0, rfl⟩
        have hord : orderOf (e.some x0) = orderOf x0 := e.some.orderOf_eq x0
        change Odd (orderOf (e.some x0))
        rw [hord]
        exact hXodd x0 hx0
      have hX0cent : X.map e.some.toMonoidHom ≤
          Subgroup.centralizer ({tP} : Set (PSL2 K)) := by
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨x0, hx0, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hxcent : x0 ∈ Subgroup.centralizer ({tQ} : Set Q) := hXcent hx0
        have hcomm : x0 * tQ = tQ * x0 :=
          Subgroup.mem_centralizer_singleton_iff.mp hxcent
        have hP : e.some x0 * tP = tP * e.some x0 := by
          calc
            e.some x0 * tP = e.some x0 * e.some tQ := rfl
            _ = e.some (x0 * tQ) := by rw [map_mul]
            _ = e.some (tQ * x0) := by rw [hcomm]
            _ = e.some tQ * e.some x0 := by rw [map_mul]
            _ = tP * e.some x0 := rfl
        exact hP
      have hX0T0 : X.map e.some.toMonoidHom ≤ T0 :=
        hT0contain (X.map e.some.toMonoidHom) hX0 hX0cent
      intro x hx
      have hxP : e.some x ∈ T0 := hX0T0 (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      exact Subgroup.mem_map.mpr ⟨e.some x, hxP, by
        change e.some.symm.toMonoidHom (e.some x) = x
        simp⟩
    have hCcardQ : Nat.card (Subgroup.centralizer ({tQ} : Set Q)) =
        2 * Nat.card T := by
      have hCmap : (Subgroup.centralizer ({tP} : Set (PSL2 K))).map
            e.some.symm.toMonoidHom = Subgroup.centralizer ({tQ} : Set Q) := by
        ext y
        constructor
        · intro hy
          rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hcomm : x * tP = tP * x :=
            Subgroup.mem_centralizer_singleton_iff.mp hx
          apply e.some.injective
          calc
            e.some (e.some.symm x * tQ) = x * tP := by simp [tP]
            _ = tP * x := hcomm
            _ = e.some (tQ * e.some.symm x) := by simp [tP]
        · intro hy
          have hx : e.some y ∈ Subgroup.centralizer ({tP} : Set (PSL2 K)) := by
            rw [Subgroup.mem_centralizer_singleton_iff]
            have hcomm : y * tQ = tQ * y :=
              Subgroup.mem_centralizer_singleton_iff.mp hy
            dsimp [tP]
            rw [← map_mul, ← map_mul]
            exact congrArg e.some hcomm
          exact Subgroup.mem_map.mpr ⟨e.some y, hx, by
            change e.some.symm.toMonoidHom (e.some y) = y
            simp⟩
      have hCcardT0 : Nat.card (Subgroup.centralizer ({tP} : Set (PSL2 K))) =
          Nat.card (Subgroup.centralizer ({tQ} : Set Q)) := by
        rw [← hCmap]
        exact (Subgroup.card_map_of_injective
          (K := Subgroup.centralizer ({tP} : Set (PSL2 K)))
          (f := e.some.symm.toMonoidHom) e.some.symm.injective).symm
      have hTeq : Nat.card T = Nat.card T0 := by
        rw [hTcard, hT0card]
      calc
        Nat.card (Subgroup.centralizer ({tQ} : Set Q)) =
            Nat.card (Subgroup.centralizer ({tP} : Set (PSL2 K))) :=
          hCcardT0.symm
        _ = 2 * Nat.card T0 := hCcard
        _ = 2 * Nat.card T := by rw [hTeq]
    have hTnormcard : Nat.card
        (Subgroup.normalizer (T : Set Q)) = 2 * Nat.card T := by
      simpa [T] using normalizer_card_of_map_equiv T0 e.some.symm hT0normcard
    exact ⟨⟨hKfull, e, T, hTcyc, htQ_T, hTeven,
      Or.inr hTcard, hTcontain, hCcardQ, hTnormcard⟩⟩

end CFSG.GorensteinWalter
