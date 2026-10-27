module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Center
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center

namespace CFSG
end CFSG
open CFSG

/-!
# Section 2 preamble equality `H = S U`

This lower, acyclic module proves the recalled equality used by
`Section2.Basic`.  The route is:

* `S ≤ H` gives a Sylow-2 subgroup of `H` by restriction;
* a central involution survives in `H/O_{2'}(H)`;
* the `A₇` and linear branches of `IsDGroup H` are impossible because their
  relevant centers are trivial;
* the remaining quotient is a 2-group, and the Sylow image plus the odd core
  generate `H`.

It also owns the reusable setup lemma `centralizerSetup_S_le_H`, shared with
the documentation module `Section2.Preamble`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open Matrix
open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise

/-! ## Setup infrastructure: `S ≤ H` (`t` is central in `S`) -/
/-- In a cyclic group of order `2^m` with `m ≥ 1`, every two involutions
coincide.  Proof: with a generator `g`, every involution equals
`g ^ (2 ^ (m - 1))`. -/
private lemma unique_involution_of_cyclic_two_group {A : Type*} [Group A] [Finite A]
    (hcyc : IsCyclic A) {m : ℕ} (hm : 1 ≤ m)
    (hcard : Nat.card A = 2 ^ m) :
    ∀ x y : A, x ≠ 1 → x ^ 2 = 1 → y ≠ 1 → y ^ 2 = 1 → x = y := by
  classical
  let : IsCyclic A := hcyc
  rcases IsCyclic.exists_monoid_generator (α := A) with ⟨g, hg⟩
  have hord : orderOf g = 2 ^ m := by
    rw [← hcard]
    apply orderOf_eq_card_of_forall_mem_zpowers
    intro x
    rcases hg x with ⟨k, rfl⟩
    exact ⟨k, zpow_natCast g k⟩
  have hmm : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have h2m : 2 * 2 ^ (m - 1) = 2 ^ m := by
    calc
      2 * 2 ^ (m - 1) = 2 ^ (m - 1) * 2 := by rw [Nat.mul_comm]
      _ = 2 ^ (m - 1 + 1) := by exact (pow_succ 2 (m - 1)).symm
      _ = 2 ^ m := by rw [hmm]
  have hgpow : g ^ (2 ^ m) = 1 := by
    exact (orderOf_dvd_iff_pow_eq_one (x := g) (n := 2 ^ m)).1 (by simp [hord])
  have h2h : (g ^ (2 ^ (m - 1))) ^ 2 = 1 := by
    calc
      (g ^ (2 ^ (m - 1))) ^ 2 = g ^ (2 ^ (m - 1) * 2) := by
        exact (pow_mul g (2 ^ (m - 1)) 2).symm
      _ = g ^ (2 * 2 ^ (m - 1)) := by rw [Nat.mul_comm]
      _ = g ^ (2 ^ m) := by rw [h2m]
      _ = 1 := hgpow
  have h_pow_odd : ∀ k : ℕ, (g ^ (2 ^ (m - 1))) ^ (2 * k + 1) = g ^ (2 ^ (m - 1)) := by
    intro k
    calc
      (g ^ (2 ^ (m - 1))) ^ (2 * k + 1) =
          (g ^ (2 ^ (m - 1))) ^ (2 * k) * g ^ (2 ^ (m - 1)) := by
        exact pow_succ (g ^ (2 ^ (m - 1))) (2 * k)
      _ = ((g ^ (2 ^ (m - 1))) ^ 2) ^ k * g ^ (2 ^ (m - 1)) := by
        exact congrArg (fun z : A => z * g ^ (2 ^ (m - 1)))
          (pow_mul (g ^ (2 ^ (m - 1))) 2 k)
      _ = 1 ^ k * g ^ (2 ^ (m - 1)) := by rw [h2h]
      _ = g ^ (2 ^ (m - 1)) := by simp
  intro x y hx1 hx2 hy1 hy2
  rcases hg x with ⟨a, rfl⟩
  rcases hg y with ⟨b, rfl⟩
  have hxa : orderOf g ∣ 2 * a := by
    apply (orderOf_dvd_iff_pow_eq_one (x := g) (n := 2 * a)).2
    simpa [pow_mul, Nat.mul_comm] using hx2
  have hya : orderOf g ∣ 2 * b := by
    apply (orderOf_dvd_iff_pow_eq_one (x := g) (n := 2 * b)).2
    simpa [pow_mul, Nat.mul_comm] using hy2
  have hdiv_a : 2 ^ (m - 1) ∣ a := by
    rw [hord] at hxa
    rw [← h2m] at hxa
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hxa
  have hdiv_b : 2 ^ (m - 1) ∣ b := by
    rw [hord] at hya
    rw [← h2m] at hya
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hya
  rcases hdiv_a with ⟨a', rfl⟩
  rcases hdiv_b with ⟨b', rfl⟩
  have hx_ne : (g ^ (2 ^ (m - 1))) ^ a' ≠ 1 := by
    simpa [pow_mul] using hx1
  have hy_ne : (g ^ (2 ^ (m - 1))) ^ b' ≠ 1 := by
    simpa [pow_mul] using hy1
  have hodd_a : Odd a' := by
    rcases Nat.even_or_odd a' with he | ho
    · exfalso
      rcases he with ⟨k, rfl⟩
      have hkk : (g ^ (2 ^ (m - 1))) ^ (k + k) = 1 := by
        calc
          (g ^ (2 ^ (m - 1))) ^ (k + k) = (g ^ (2 ^ (m - 1))) ^ (2 * k) := by
            rw [Nat.two_mul]
          _ = ((g ^ (2 ^ (m - 1))) ^ 2) ^ k := by
            exact pow_mul (g ^ (2 ^ (m - 1))) 2 k
          _ = 1 ^ k := by rw [h2h]
          _ = 1 := by simp
      exact hx_ne hkk
    · exact ho
  have hodd_b : Odd b' := by
    rcases Nat.even_or_odd b' with he | ho
    · exfalso
      rcases he with ⟨k, rfl⟩
      have hkk : (g ^ (2 ^ (m - 1))) ^ (k + k) = 1 := by
        calc
          (g ^ (2 ^ (m - 1))) ^ (k + k) = (g ^ (2 ^ (m - 1))) ^ (2 * k) := by
            rw [Nat.two_mul]
          _ = ((g ^ (2 ^ (m - 1))) ^ 2) ^ k := by
            exact pow_mul (g ^ (2 ^ (m - 1))) 2 k
          _ = 1 ^ k := by rw [h2h]
          _ = 1 := by simp
      exact hy_ne hkk
    · exact ho
  rcases hodd_a with ⟨ka, rfl⟩
  rcases hodd_b with ⟨kb, rfl⟩
  calc
    g ^ (2 ^ (m - 1) * (2 * ka + 1)) = (g ^ (2 ^ (m - 1))) ^ (2 * ka + 1) := by
      exact pow_mul g (2 ^ (m - 1)) (2 * ka + 1)
    _ = g ^ (2 ^ (m - 1)) := h_pow_odd ka
    _ = (g ^ (2 ^ (m - 1))) ^ (2 * kb + 1) := (h_pow_odd kb).symm
    _ = g ^ (2 ^ (m - 1) * (2 * kb + 1)) := by
      exact (pow_mul g (2 ^ (m - 1)) (2 * kb + 1)).symm

/-- `t` is centralized by the Sylow `2`-subgroup `S`: `t` is the unique
involution of the cyclic index-2 subgroup `S0` of the dihedral group `S`, and
every conjugate of `t` by an element of `S` is again an involution of `S0`. -/
private lemma t_mem_center_S {G : Type u} [Group G] [Finite G] (c : CentralizerSetup G) :
    ∀ s : G, s ∈ (c.S : Subgroup G) → c.t * s * c.t⁻¹ = s := by
  classical
  let S' : Subgroup G := c.S
  let S0' : Subgroup (↥S') := c.S0.subgroupOf S'
  have hmap : (c.S0.subgroupOf (c.S : Subgroup G)).map (c.S : Subgroup G).subtype = c.S0 := by
    ext y
    constructor
    · intro hy
      rcases (Subgroup.mem_map.mp hy) with ⟨x, hx, rfl⟩
      exact (Subgroup.mem_subgroupOf.mp hx)
    · intro hy
      refine Subgroup.mem_map.mpr ⟨⟨y, c.S0_le_S hy⟩, ?_⟩
      constructor
      · exact (Subgroup.mem_subgroupOf (H := c.S0) (K := (c.S : Subgroup G))
          (h := ⟨y, c.S0_le_S hy⟩)).mpr hy
      · rfl
  have hS0'_index : (c.S0.subgroupOf (c.S : Subgroup G)).index = 2 := by
    have h1 := Subgroup.card_mul_index (c.S0.subgroupOf (c.S : Subgroup G))
    have hc : Nat.card ↥(c.S0.subgroupOf (c.S : Subgroup G)) = Nat.card ↥c.S0 := by
      have hcs := Subgroup.card_subtype (c.S : Subgroup G) (c.S0.subgroupOf (c.S : Subgroup G))
      rw [hmap] at hcs
      exact hcs.symm
    rw [hc, c.S_index_two] at h1
    have hpos : 0 < Nat.card ↥c.S0 := Nat.card_pos
    exact Nat.mul_right_cancel hpos (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h1)
  have hS0'_normal : S0'.Normal := by
    apply Subgroup.normal_of_index_eq_two
    exact hS0'_index
  have hcardS : Nat.card ↥(c.S : Subgroup G) = 2 * 2 ^ c.m := by
    rcases c.dihedralEquiv with ⟨e⟩
    calc
      Nat.card ↥(c.S : Subgroup G) = Nat.card (DihedralGroup (2 ^ c.m)) := by
        exact Nat.card_congr e.toEquiv
      _ = 2 * 2 ^ c.m := by
        rw [Nat.card_eq_fintype_card]
        exact DihedralGroup.card
  have hcardS0 : Nat.card ↥c.S0 = 2 ^ c.m := by
    have h1 : Nat.card ↥(c.S : Subgroup G) = 2 * Nat.card ↥c.S0 := c.S_index_two
    rw [hcardS] at h1
    have h2 : 2 ^ c.m = Nat.card ↥c.S0 := by
      exact Nat.mul_left_cancel (by norm_num) h1
    exact h2.symm
  have huniq : ∀ x y : ↥c.S0, x ≠ 1 → x ^ 2 = 1 → y ≠ 1 → y ^ 2 = 1 → x = y :=
    unique_involution_of_cyclic_two_group c.S0_cyclic c.one_le_m hcardS0
  intro s hs
  let sS : ↥S' := ⟨s, hs⟩
  let tS : ↥S' := ⟨c.t, c.S0_le_S c.t_mem_S0⟩
  have htS' : tS ∈ S0' := by
    simpa [S0', S', tS, Subgroup.mem_subgroupOf] using c.t_mem_S0
  have hconj : sS * tS * sS⁻¹ ∈ S0' := hS0'_normal.conj_mem tS htS' sS
  let x : ↥c.S0 := ⟨s * c.t * s⁻¹, by
    simpa [sS, tS, S0', S', Subgroup.mem_subgroupOf] using hconj⟩
  let y : ↥c.S0 := ⟨c.t, c.t_mem_S0⟩
  have hx1 : x ≠ 1 := by
    intro hx
    apply c.t_involution.1
    have hval : s * c.t * s⁻¹ = 1 := by
      simpa [x] using congrArg Subtype.val hx
    calc
      c.t = s⁻¹ * (s * c.t * s⁻¹) * s := by group
      _ = s⁻¹ * 1 * s := by rw [hval]
      _ = 1 := by simp
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    have ht2 : c.t * c.t = 1 := by simpa [pow_two] using c.t_involution.2
    calc
      (s * c.t * s⁻¹) ^ 2 = (s * c.t * s⁻¹) * (s * c.t * s⁻¹) := by rw [pow_two]
      _ = s * c.t * (s⁻¹ * s) * c.t * s⁻¹ := by group
      _ = s * (c.t * c.t) * s⁻¹ := by group
      _ = s * 1 * s⁻¹ := by rw [ht2]
      _ = 1 := by simp
  have hy1 : y ≠ 1 := by
    intro hy
    apply c.t_involution.1
    simpa [y] using congrArg Subtype.val hy
  have hy2 : y ^ 2 = 1 := by
    apply Subtype.ext
    simpa [y, pow_two] using c.t_involution.2
  have heq : x = y := huniq x y hx1 hx2 hy1 hy2
  have hval : s * c.t * s⁻¹ = c.t := by
    simpa [x, y] using congrArg Subtype.val heq
  have hcomm : c.t * s = s * c.t := by
    calc
      c.t * s = s * c.t * s⁻¹ * s := by rw [hval]
      _ = s * c.t := by group
  calc
    c.t * s * c.t⁻¹ = (s * c.t) * c.t⁻¹ := by rw [hcomm]
    _ = s := by group

/-- `S ≤ H = C_G(t)`: the fixed Sylow `2`-subgroup lies in the centralizer of
`t`.  This is the easy inclusion in the paper's `H = SU` (p. 219); the full
equality is proved below as `fact_2_preamble_H_eq_SU_proved`. -/
public theorem centralizerSetup_S_le_H {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : (c.S : Subgroup G) ≤ c.H := by
  intro s hs
  have ht : c.t * s * c.t⁻¹ = s := t_mem_center_S c s hs
  rw [c.H_eq_centralizer]
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzt : z = c.t := by simpa using hz
  rw [hzt]
  calc
    c.t * s = (c.t * s * c.t⁻¹) * c.t := by group
    _ = s * c.t := by rw [ht]

/-! ## Sylow restriction and quotient generation -/

/-- Restrict a Sylow subgroup along an inclusion of subgroups. -/
public def preambleSylowOfLe {G : Type*} [Group G] {p : ℕ}
    (P : Sylow p G) (H : Subgroup G) (hPH : (P : Subgroup G) ≤ H) : Sylow p H := by
  refine
    { toSubgroup := (P : Subgroup G).subgroupOf H
      isPGroup' := ?_
      is_maximal' := ?_ }
  · exact P.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  · intro Q hQ hPQ
    have hQmap : IsPGroup p (Q.map H.subtype) := hQ.map H.subtype
    have hPmap : (P : Subgroup G) ≤ Q.map H.subtype := by
      intro x hx
      have hxH : x ∈ H := hPH hx
      have hxPQ : (⟨x, hxH⟩ : H) ∈ (P : Subgroup G).subgroupOf H := hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, hPQ hxPQ, rfl⟩
    have hmap : Q.map H.subtype = (P : Subgroup G) := P.is_maximal' hQmap hPmap
    apply (Subgroup.map_subtype_inj).mp
    rw [hmap, Subgroup.map_subgroupOf_eq_of_le hPH]

/-- If `U ◃ H` and `H/U` is a 2-group, a Sylow-2 subgroup of `H` together
with `U` generates `H`. -/
public theorem preambleSylow_sup_of_quotient_pgroup
    {H : Type*} [Group H] [Finite H]
    (U : Subgroup H) [U.Normal] (P : Sylow 2 H)
    (hQ : IsPGroup 2 (H ⧸ U)) : (P : Subgroup H) ⊔ U = ⊤ := by
  let f : H →* H ⧸ U := QuotientGroup.mk' U
  let Q : Sylow 2 (H ⧸ U) := P.mapSurjective (QuotientGroup.mk'_surjective U)
  have hQtop : (Q : Subgroup (H ⧸ U)) = ⊤ := by
    have htopP : IsPGroup 2 (⊤ : Subgroup (H ⧸ U)) := hQ.to_subgroup ⊤
    exact (Q.is_maximal' htopP le_top).symm
  have hmap : (P : Subgroup H).map f = ⊤ := by
    change (Q : Subgroup (H ⧸ U)) = ⊤
    exact hQtop
  have hcomap : (P : Subgroup H) ⊔ f.ker = ⊤ := by
    have h := Subgroup.comap_map_eq f (P : Subgroup H)
    rw [hmap, Subgroup.comap_top] at h
    exact h.symm
  simpa [f, QuotientGroup.ker_mk'] using hcomap

/-! ## The central involution in the odd-core quotient -/

/-- The involution selected in a `CentralizerSetup` is central in `H`. -/
public lemma preambleCentralInvolutionInH {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (hSle : (c.S : Subgroup G) ≤ c.H) :
    let tH : ↥c.H := ⟨c.t, hSle (c.S0_le_S c.t_mem_S0)⟩
    tH ∈ Subgroup.center (↥c.H) := by
  dsimp
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  have hx : (x : G) ∈ Subgroup.centralizer ({c.t} : Set G) := by
    rw [← c.H_eq_centralizer]
    exact x.property
  have hcomm := (Subgroup.mem_centralizer_iff.mp hx) c.t (by simp)
  exact hcomm.symm

/-- A nontrivial central involution of `H` remains a nontrivial central
involution after quotienting by the odd core `O_{2'}(H)`. -/
public lemma preambleCentralInvolutionQuotient
    {H : Type*} [Group H] [Finite H]
    (t : H) (htcenter : t ∈ Subgroup.center H)
    (ht2 : t ^ 2 = 1) (htne : t ≠ 1) :
    let U := pPrimeCore 2 H
    let q : H →* (H ⧸ U) := QuotientGroup.mk' U
    let tb := q t
    tb ∈ Subgroup.center (H ⧸ U) ∧ tb ^ 2 = 1 ∧ tb ≠ 1 := by
  let U : Subgroup H := pPrimeCore 2 H
  let q : H →* (H ⧸ U) := QuotientGroup.mk' U
  let tb : H ⧸ U := q t
  have htbc : tb ∈ Subgroup.center (H ⧸ U) := by
    rw [Subgroup.mem_center_iff]
    intro y
    rcases (QuotientGroup.mk'_surjective U y) with ⟨x, rfl⟩
    simpa [tb, q, map_mul] using congrArg q ((Subgroup.mem_center_iff.mp htcenter) x)
  have htb2 : tb ^ 2 = 1 := by
    simpa [tb, q] using congrArg q ht2
  have htbne : tb ≠ 1 := by
    intro h
    have htU : t ∈ U := by
      apply (QuotientGroup.eq_one_iff (N := U) t).mp
      simpa [tb, q] using h
    have hUcop : Nat.Coprime 2 (Nat.card U) := by
      dsimp [U]
      exact pPrimeCore_coprime_card (p := 2) (G := H)
    have horder : orderOf t = 2 := orderOf_eq_prime ht2 htne
    have hdiv : orderOf t ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U htU
    rw [horder] at hdiv
    have hbad : 2 = 1 := hUcop.eq_one_of_dvd hdiv
    omega
  exact ⟨htbc, htb2, htbne⟩

/-! ## D-group branch elimination -/

public lemma preambleCenter_eq_bot_A7 :
    Subgroup.center (alternatingGroup (Fin 7)) = ⊥ := by
  exact alternatingGroup.center_eq_bot (by norm_num)

public lemma preambleCenter_mem_map
    {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    {a : A} (ha : a ∈ Subgroup.center A) : e a ∈ Subgroup.center B := by
  rw [Subgroup.mem_center_iff]
  intro b
  rcases e.surjective b with ⟨x, rfl⟩
  simpa [map_mul] using congrArg e (Subgroup.mem_center_iff.mp ha x)

/-- The odd-index normal linear subgroup in the linear `IsDGroup` branch
contains every element of order two. -/
public lemma preamble_mem_of_odd_index
    {Q : Type*} [Group Q] [Finite Q]
    (L : Subgroup Q) (hLnormal : L.Normal) (hLindex : Odd L.index)
    {t : Q} (ht2 : t ^ 2 = 1) : t ∈ L := by
  let q : Q →* (Q ⧸ L) := QuotientGroup.mk' L
  have hq2 : (q t) ^ 2 = 1 := by simpa [q] using congrArg q ht2
  have horder : orderOf (q t) ∣ 2 := orderOf_dvd_of_pow_eq_one hq2
  let : Fintype (Q ⧸ L) := Fintype.ofFinite (Q ⧸ L)
  have horder_card : orderOf (q t) ∣ Fintype.card (Q ⧸ L) := orderOf_dvd_card
  have hcard_index : Fintype.card (Q ⧸ L) = L.index := by
    simpa [Nat.card_eq_fintype_card] using (Subgroup.index_eq_card L).symm
  have hoddcard : Odd (Fintype.card (Q ⧸ L)) := by simpa [hcard_index] using hLindex
  rcases (Nat.dvd_prime Nat.prime_two).mp horder with h1 | h2
  · have hqone : q t = 1 := by
      exact (orderOf_eq_one_iff.mp h1)
    exact (QuotientGroup.eq_one_iff t).mp (by simpa [q] using hqone)
  · exfalso
    have h2dvd : 2 ∣ L.index := by simpa [h2, hcard_index] using horder_card
    exact (Nat.not_even_iff_odd.mpr hLindex) (even_iff_two_dvd.mpr h2dvd)

public theorem preambleCentralInvolution_quotient_two_of_dgroup
    {H : Type u} [Group H] [Finite H]
    (hD : IsDGroup H)
    {t : H} (htcenter : t ∈ Subgroup.center H)
    (ht2 : t ^ 2 = 1) (htne : t ≠ 1) :
    IsPGroup 2 (H ⧸ pPrimeCore 2 H) := by
  let U : Subgroup H := pPrimeCore 2 H
  let Q : Type u := H ⧸ U
  let q : H →* Q := QuotientGroup.mk' U
  let tb : Q := q t
  have htq : tb ∈ Subgroup.center Q := by
    simpa [tb, q, Q, U] using
      (preambleCentralInvolutionQuotient t htcenter ht2 htne).1
  have htq2 : tb ^ 2 = 1 := by
    simpa [tb, q, Q, U] using
      (preambleCentralInvolutionQuotient t htcenter ht2 htne).2.1
  have htqne : tb ≠ 1 := by
    simpa [tb, q, Q, U] using
      (preambleCentralInvolutionQuotient t htcenter ht2 htne).2.2
  rcases hD with ⟨_hSylow, htwo⟩ | ⟨_hSylow, e7⟩ |
      ⟨_hSylow, K, _hKprime, L, hLnormal, hLindex, hLmodel⟩
  · simpa [Q, U] using htwo
  ·
    have hecenter : e7.some tb ∈ Subgroup.center (alternatingGroup (Fin 7)) :=
      preambleCenter_mem_map e7.some htq
    have heone : e7.some tb = 1 := by
      have hempty : e7.some tb ∈ (⊥ : Subgroup (alternatingGroup (Fin 7))) := by
        simpa [preambleCenter_eq_bot_A7] using hecenter
      exact Subgroup.mem_bot.mp hempty
    exfalso
    apply htqne
    apply e7.some.injective
    simpa using heone
  ·
    let : L.Normal := hLnormal
    have htL : tb ∈ L := preamble_mem_of_odd_index L hLnormal hLindex htq2
    let tbL : ↥L := ⟨tb, htL⟩
    have htLc : tbL ∈ Subgroup.center (↥L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp htq) (y : Q)
    rcases hLmodel with hpsl | hpgl
    · have hmodelc : hpsl.some tbL ∈ Subgroup.center (PSL2 K) :=
        preambleCenter_mem_map hpsl.some htLc
      have hmodelone : hpsl.some tbL = 1 := by
        have hmempty : hpsl.some tbL ∈ (⊥ : Subgroup (PSL2 K)) := by
          simpa [psl2_center_eq_bot] using hmodelc
        exact Subgroup.mem_bot.mp hmempty
      exfalso
      apply htqne
      have htbLeone : tbL = 1 := hpsl.some.injective (by simpa using hmodelone)
      simpa [tbL] using congrArg (fun z : ↥L => (z : Q)) htbLeone
    · have hmodelc : hpgl.some tbL ∈ Subgroup.center (PGL2 K) :=
        preambleCenter_mem_map hpgl.some htLc
      have hmodelone : hpgl.some tbL = 1 := by
        have hmempty : hpgl.some tbL ∈ (⊥ : Subgroup (PGL2 K)) := by
          simpa [pgl2_center_eq_bot] using hmodelc
        exact Subgroup.mem_bot.mp hmempty
      exfalso
      apply htqne
      have htbLeone : tbL = 1 := hpgl.some.injective (by simpa using hmodelone)
      simpa [tbL] using congrArg (fun z : ↥L => (z : Q)) htbLeone

/-! ## Main theorem -/

/-- Lower-level proof of the Section 2 preamble equality `H = S ⊔ O(H)`.
`Section2.Basic` exposes the paper-facing theorem
`fact_2_preamble_H_eq_SU` as a wrapper around this acyclic declaration. -/
public theorem fact_2_preamble_H_eq_SU_proved
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) :
    (c.S : Subgroup G) ⊔ c.U = c.H := by
  have hSle : (c.S : Subgroup G) ≤ c.H := centralizerSetup_S_le_H c
  have hHproper : c.H ≠ ⊤ := by
    intro htop
    have hhat : c.Hhat = ⊤ := by
      apply top_unique
      rw [← htop]
      exact c.H_le_Hhat
    exact c.Hhat_maximal.ne_top hhat
  have hD : IsDGroup (↥c.H) := properSubgroups_areDGroups hmin c.H hHproper
  let P : Sylow 2 (↥c.H) := preambleSylowOfLe c.S c.H hSle
  have htH : (⟨c.t, hSle (c.S0_le_S c.t_mem_S0)⟩ : ↥c.H) ∈
      Subgroup.center (↥c.H) := preambleCentralInvolutionInH c hSle
  have htH2 : (⟨c.t, hSle (c.S0_le_S c.t_mem_S0)⟩ : ↥c.H) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two, Subgroup.coe_mul] using c.t_involution.2
  have htHne : (⟨c.t, hSle (c.S0_le_S c.t_mem_S0)⟩ : ↥c.H) ≠ 1 := by
    intro h
    apply c.t_involution.1
    exact congrArg (fun z : ↥c.H => (z : G)) h
  have hQ : IsPGroup 2 ((↥c.H) ⧸ pPrimeCore 2 (↥c.H)) :=
    preambleCentralInvolution_quotient_two_of_dgroup hD htH htH2 htHne
  have hjoin : (P : Subgroup (↥c.H)) ⊔ pPrimeCore 2 (↥c.H) = ⊤ :=
    preambleSylow_sup_of_quotient_pgroup (pPrimeCore 2 (↥c.H)) P hQ
  have hPmap : (P : Subgroup (↥c.H)).map c.H.subtype = (c.S : Subgroup G) := by
    have hPcoe : (P : Subgroup (↥c.H)) = (c.S : Subgroup G).subgroupOf c.H := by
      simp [P, preambleSylowOfLe]
    rw [hPcoe]
    exact Subgroup.map_subgroupOf_eq_of_le hSle
  have hmapjoin := congrArg (Subgroup.map c.H.subtype) hjoin
  have htopmap : Subgroup.map c.H.subtype (⊤ : Subgroup (↥c.H)) = c.H := by
    simpa using (Subgroup.map_subgroupOf_eq_of_le (H := c.H) (K := c.H) le_rfl)
  rw [htopmap] at hmapjoin
  simpa [Subgroup.map_sup, hPmap, oddCoreOf, CentralizerSetup.U] using hmapjoin

end CFSG.GorensteinWalter
