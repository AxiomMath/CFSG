module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralUniqueCentralInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralNormalSubgroup

namespace CFSG
end CFSG
open CFSG

/-!
# Index-two and O²(M)-branch infrastructure for Lemma 2.7

This leaf module owns the generic normal-index-two machinery (sign of the
left regular representation, index-two overgroups, odd-index Sylow
containment) and the closure of the `t ∈ O²(M)` trichotomy cases that only
depend on index parity.  It sits below `Lemma27Infra` so those helpers can be
iterated quickly without rebuilding the whole Section-2 chain.
-/

namespace CFSG.GorensteinWalter

universe u

noncomputable section

open scoped Pointwise

/-! ## The `t ∈ O²(M)` branch: trichotomy infrastructure -/

/-- A Sylow `2`-subgroup lies in every normal odd-index subgroup (generic
version of `Theorem26Core.sylow_le_of_normal_odd_index_local`, kept local to
avoid the `Theorem26 → Lemma22 → ... → Lemma27Infra` import cycle). -/
public theorem sylow_le_of_normal_odd_index_local_27
    {Q : Type u} [Group Q] [Finite Q]
    (L : Subgroup Q) (hLnormal : L.Normal) (hLindex : Odd L.index)
    (P : Sylow 2 Q) : (P : Subgroup Q) ≤ L := by
  let : L.Normal := hLnormal
  let pi : Q →* Q ⧸ L := QuotientGroup.mk' L
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmapP : IsPGroup 2 ((P : Subgroup Q).map pi) :=
    P.isPGroup'.map pi
  rcases IsPGroup.iff_card.mp hmapP with ⟨n, hn⟩
  have hcard_dvd : Nat.card ((P : Subgroup Q).map pi) ∣ Nat.card (Q ⧸ L) :=
    Subgroup.card_subgroup_dvd_card ((P : Subgroup Q).map pi)
  have hquot_odd : Odd (Nat.card (Q ⧸ L)) := by
    simpa only [Subgroup.index_eq_card] using hLindex
  cases n with
  | zero =>
      have hmap_bot : (P : Subgroup Q).map pi = ⊥ := by
        exact Subgroup.eq_bot_of_card_eq
          ((P : Subgroup Q).map pi) (by simpa using hn)
      have hle_ker : (P : Subgroup Q) ≤ pi.ker :=
        (Subgroup.map_eq_bot_iff (H := (P : Subgroup Q)) (f := pi)).mp hmap_bot
      simpa [pi, QuotientGroup.ker_mk'] using hle_ker
  | succ n =>
      have htwo_dvd_map : 2 ∣ Nat.card ((P : Subgroup Q).map pi) := by
        rw [hn]
        exact dvd_pow_self 2 (Nat.succ_ne_zero n)
      exact False.elim
        (hquot_odd.not_two_dvd_nat (htwo_dvd_map.trans hcard_dvd))

/-- An involution of `M` lies in every normal subgroup of odd index, because
that subgroup contains a Sylow `2`-subgroup of `M` containing the involution. -/
public theorem t_mem_N_map_of_index_odd
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) {t : G} (htM : t ∈ M) (ht : IsInvolution t)
    {N : Subgroup (↥M)} (hN : N.Normal) (hodd : Odd N.index) :
    t ∈ N.map M.subtype := by
  classical
  let tM : ↥M := ⟨t, htM⟩
  have htp : IsPGroup 2 (Subgroup.zpowers tM) := by
    apply IsPGroup.of_card (n := 1)
    have hord : orderOf tM = 2 := orderOf_eq_prime
      (by apply Subtype.ext; exact ht.2)
      (by intro h; apply ht.1; exact congrArg Subtype.val h)
    simp [Nat.card_zpowers, hord]
  obtain ⟨P, hTleP⟩ := IsPGroup.exists_le_sylow (G := ↥M) (p := 2) htp
  have hPleN : (P : Subgroup (↥M)) ≤ N :=
    sylow_le_of_normal_odd_index_local_27 N hN hodd P
  exact Subgroup.mem_map.mpr
    ⟨tM, hPleN (hTleP (Subgroup.mem_zpowers tM)), rfl⟩

/-- The odd core of a subgroup has odd order. -/
public theorem odd_card_oddCoreOf
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) :
    Odd (Nat.card (↥(oddCoreOf M))) := by
  have hcard : Nat.card (↥(oddCoreOf M)) =
      Nat.card (↥(pPrimeCore 2 (↥M))) := by
    unfold oddCoreOf
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective (pPrimeCore 2 (↥M)) M.subtype
        M.subtype_injective).toEquiv.symm
  rw [hcard]
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥M))

/-- An involution cannot lie in a subgroup of odd order. -/
public theorem not_mem_odd_order_subgroup_of_involution
    {G : Type u} [Group G] [Finite G]
    {t : G} (ht : IsInvolution t) {H : Subgroup G}
    (hodd : Odd (Nat.card (↥H))) :
    t ∉ H := by
  intro htH
  have hord2 : orderOf t ∣ 2 :=
    (orderOf_dvd_iff_pow_eq_one (x := t) (n := 2)).2 ht.2
  have hordH : orderOf t ∣ Nat.card (↥H) :=
    Subgroup.orderOf_dvd_natCard H htH
  have hdvd : orderOf t ∣ (2 : ℕ).gcd (Nat.card (↥H)) :=
    Nat.dvd_gcd hord2 hordH
  have hgcd : (2 : ℕ).gcd (Nat.card (↥H)) = 1 := by
    simpa [Nat.gcd_comm] using hodd.coprime_two_left.gcd_eq_one
  have ht1 : t = 1 :=
    (orderOf_eq_one_iff).mp (Nat.dvd_one.mp (by simpa [hgcd] using hdvd))
  exact ht.1 ht1

/-- If `M/O₂'(M)` is a `2`-group (the normal-`2`-complement situation), then
`O²(M) ≤ O₂'(M)`.  Combined with the oddness of `O₂'(M)`, this makes the
`t ∈ O²(M)` branch contradictory in the index-four trichotomy case. -/
public theorem twoResidualOf_le_oddCoreOf_of_normalPComplement
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (hNPC : Glauberman.NormalPComplement 2 (↥M)) :
    twoResidualOf M ≤ oddCoreOf M := by
  classical
  have hQ : IsPGroup 2 ((↥M) ⧸ pPrimeCore 2 (↥M)) :=
    isPGroup_quotient_pPrimeCore_of_normalPComplement hNPC
  rcases IsPGroup.iff_card.mp hQ with ⟨n, hn⟩
  have hidx : (pPrimeCore 2 (↥M)).index = 2 ^ n := by
    rw [Subgroup.index_eq_card, hn]
  have hle := pResidualOf_le_of_normal_index (H := M) (p := 2)
    (N := pPrimeCore 2 (↥M)) (by infer_instance) ⟨n, hidx⟩
  change pResidualOf M 2 ≤ (pPrimeCore 2 (↥M)).map M.subtype
  exact hle

/-- If `M/O₂'(M)` is a `2`-group, then `O²(M) ≤ O₂'(M)`.  This is the
quotient-side variant of `twoResidualOf_le_oddCoreOf_of_normalPComplement`,
used to rule out the two-group quotient in the first two trichotomy cases. -/
public theorem twoResidualOf_le_oddCoreOf_of_isPGroup_quotient
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (hQ : IsPGroup 2 ((↥M) ⧸ pPrimeCore 2 (↥M))) :
    twoResidualOf M ≤ oddCoreOf M := by
  classical
  rcases IsPGroup.iff_card.mp hQ with ⟨n, hn⟩
  have hidx : (pPrimeCore 2 (↥M)).index = 2 ^ n := by
    rw [Subgroup.index_eq_card, hn]
  have hle := pResidualOf_le_of_normal_index (H := M) (p := 2)
    (N := pPrimeCore 2 (↥M)) (by infer_instance) ⟨n, hidx⟩
  change pResidualOf M 2 ≤ (pPrimeCore 2 (↥M)).map M.subtype
  exact hle

/-- A finite group of order `2 · odd` has a normal subgroup of index two
(sign of the left regular representation). -/
public theorem exists_normal_index_two_of_card_eq_two_mul_odd
    {G : Type u} [Group G] [Finite G]
    (h2 : 2 ∣ Nat.card G) (hodd : Odd (Nat.card G / 2)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have h2' : 2 ∣ Fintype.card G := by
    simpa [Nat.card_eq_fintype_card] using h2
  obtain ⟨g, hg2⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 h2
  let σ : Equiv.Perm G := MulAction.toPerm (β := G) g
  have hσ2 : σ ^ 2 = 1 := by
    ext x
    change g * (g * x) = x
    have hg2pow : g ^ 2 = 1 :=
      (orderOf_dvd_iff_pow_eq_one (x := g) (n := 2)).1 (by rw [hg2])
    rw [← mul_assoc, ← pow_two, hg2pow, one_mul]
  have hfix_empty : ∀ x : G, x ∉ Function.fixedPoints σ := by
    intro x hx
    have hx' : g * x = x := by
      change g * x = x
      exact hx
    have hg1 : g = 1 :=
      mul_right_cancel (a := g) (b := x) (c := 1) (hx'.trans (one_mul x).symm)
    have hgne : g ≠ 1 := by
      intro h
      rw [h] at hg2
      norm_num at hg2
    exact hgne hg1
  have hfix : Function.fixedPoints σ = ∅ := by
    ext x
    constructor
    · intro hx
      exact (hfix_empty x hx).elim
    · intro hx
      simp at hx
  have hfix_card : Fintype.card (Function.fixedPoints σ) = 0 := by simp [hfix]
  have hsign : Equiv.Perm.sign σ = (-1 : ℤˣ) ^ (Nat.card G / 2) := by
    rw [Equiv.Perm.sign_of_pow_two_eq_one hσ2]
    congr 1
    simp [hfix_card, Nat.card_eq_fintype_card]
  have hsignneg : Equiv.Perm.sign σ = (-1 : ℤˣ) := by
    rw [hsign]
    exact hodd.neg_one_pow
  let ρ : G →* ℤˣ := Equiv.Perm.sign.comp (MulAction.toPermHom G G)
  have hρsurj : Function.Surjective ρ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · refine ⟨1, ?_⟩
      simp [ρ, MulAction.toPerm_one]
    · refine ⟨g, ?_⟩
      change Equiv.Perm.sign (MulAction.toPerm (β := G) g) = -1
      simpa [σ] using hsignneg
  have hindex : ρ.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hρsurj]
    simp [Nat.card_eq_fintype_card, Fintype.card_units_int]
  exact ⟨ρ.ker, inferInstance, hindex⟩

/-- If a normal subgroup has index `2 · odd`, its preimage structure gives a
normal index-two overgroup containing it. -/
public theorem exists_normal_index_two_containing_of_index_eq_two_mul_odd
    {A : Type u} [Group A] [Finite A]
    {N : Subgroup A} (hN : N.Normal)
    (h2 : 2 ∣ N.index) (hnot4 : ¬ 4 ∣ N.index) :
    ∃ M₂ : Subgroup A, M₂.Normal ∧ M₂.index = 2 ∧ N ≤ M₂ := by
  classical
  let : N.Normal := hN
  rcases h2 with ⟨m, hm⟩
  have hmodd : Odd m := by
    by_contra hnotodd
    have hEven : Even m := Nat.not_odd_iff_even.mp hnotodd
    rcases hEven with ⟨k, hk⟩
    have h4 : 4 ∣ N.index := by
      rw [hm, hk]
      use k
      ring
    exact hnot4 h4
  let Q : Type u := A ⧸ N
  have hQcard : Nat.card Q = 2 * m := by
    rw [← N.index_eq_card, hm]
  have hQ2 : 2 ∣ Nat.card Q := by
    rw [hQcard]
    exact dvd_mul_right 2 m
  have hQodd : Odd (Nat.card Q / 2) := by
    rw [hQcard]
    rw [Nat.mul_div_right _ (by norm_num : 0 < 2)]
    exact hmodd
  obtain ⟨M2q, hM2qN, hM2qidx⟩ :=
    exists_normal_index_two_of_card_eq_two_mul_odd (G := Q) hQ2 hQodd
  let M₂ : Subgroup A := M2q.comap (QuotientGroup.mk' N)
  have hM₂N : M₂.Normal := by
    dsimp [M₂]
    exact Subgroup.Normal.comap hM2qN (QuotientGroup.mk' N)
  have hM₂idx : M₂.index = 2 := by
    dsimp [M₂]
    rw [Subgroup.index_comap_of_surjective (H := M2q)
      (QuotientGroup.mk'_surjective N)]
    exact hM2qidx
  have hNleM₂ : N ≤ M₂ := by
    intro x hx
    dsimp [M₂]
    have hxq : QuotientGroup.mk' N x = (1 : Q) :=
      (QuotientGroup.eq_one_iff (N := N) (x := x)).mpr hx
    change QuotientGroup.mk' N x ∈ M2q
    rw [hxq]
    exact M2q.one_mem
  exact ⟨M₂, hM₂N, hM₂idx, hNleM₂⟩

/-- Closure of the `t ∈ O²(M)` branch in the trichotomy case with an
index-two but no index-four normal subgroup: the normal subgroup `N` of
index `2 · odd` sits in a normal index-two overgroup containing `O²(M)`,
and odd-index Sylow containment puts `t` inside `N`. -/
public theorem t_mem_N_of_mem_twoResidualOf_of_index_two_part
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) {t : G} (htM : t ∈ M) (ht : IsInvolution t)
    (hO2 : t ∈ twoResidualOf M)
    {N : Subgroup (↥M)} (hN : N.Normal) (h4 : 4 ∣ Nat.card N)
    (hNindex : ¬ 4 ∣ N.index) :
    t ∈ N.map M.subtype := by
  classical
  by_cases hodd : Odd N.index
  · exact t_mem_N_map_of_index_odd M htM ht hN hodd
  · have h2dvd : 2 ∣ N.index := by
      exact even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    rcases exists_normal_index_two_containing_of_index_eq_two_mul_odd
      (A := ↥M) (N := N) hN h2dvd hNindex with
        ⟨M₂, hM₂N, hM₂idx, hNleM₂⟩
    have hO2leM₂ : t ∈ M₂.map M.subtype := by
      have hle := pResidualOf_le_of_normal_index (H := M) (p := 2)
        (N := M₂) hM₂N ⟨1, by simpa using hM₂idx⟩
      exact hle hO2
    let tM : ↥M := ⟨t, htM⟩
    have htM₂ : tM ∈ M₂ := by
      rcases hO2leM₂ with ⟨x, hx, hxval⟩
      have hxeq : x = tM := by
        apply Subtype.ext
        simpa [tM] using hxval
      simpa [hxeq] using hx
    have htM_inv : IsInvolution tM := by
      constructor
      · intro h
        apply ht.1
        exact congrArg Subtype.val h
      · apply Subtype.ext
        exact ht.2
    have hNsub : (N.subgroupOf M₂).Normal := by
      apply (Subgroup.normal_subgroupOf_iff hNleM₂).2
      intro x m hx hm
      exact hN.conj_mem (x : ↥M) hx (m : ↥M)
    have hprod : (N.subgroupOf M₂).index * M₂.index = N.index := by
      change N.relIndex M₂ * M₂.index = N.index
      exact Subgroup.relIndex_mul_index hNleM₂
    have hmodd : Odd ((N.subgroupOf M₂).index) := by
      rcases h2dvd with ⟨m, hm⟩
      have hmodd' : Odd m := by
        by_contra hnotodd
        have hEven : Even m := Nat.not_odd_iff_even.mp hnotodd
        rcases hEven with ⟨k, hk⟩
        have h4 : 4 ∣ N.index := by
          rw [hm, hk]
          use k
          ring
        exact hNindex h4
      have hprod' : (N.subgroupOf M₂).index * 2 = 2 * m := by
        calc
          (N.subgroupOf M₂).index * 2 =
              (N.subgroupOf M₂).index * M₂.index := by rw [hM₂idx]
          _ = N.index := hprod
          _ = 2 * m := hm
      have hidx : (N.subgroupOf M₂).index = m :=
        Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
          (by simpa [mul_comm] using hprod')
      rwa [hidx]
    have hres : tM ∈ (N.subgroupOf M₂).map M₂.subtype :=
      t_mem_N_map_of_index_odd (M := M₂) (t := tM) htM₂ htM_inv hNsub hmodd
    have hmap : (N.subgroupOf M₂).map M₂.subtype = N :=
      Subgroup.map_subgroupOf_eq_of_le hNleM₂
    have htN : tM ∈ N := by
      simpa [hmap] using hres
    exact Subgroup.mem_map.mpr ⟨tM, htN, rfl⟩


end

end CFSG.GorensteinWalter
