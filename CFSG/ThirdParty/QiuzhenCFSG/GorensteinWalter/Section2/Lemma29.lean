module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

namespace CFSG
end CFSG
open CFSG

/-!
# Lemma 2.9 (Bender, "Finite Groups with Dihedral Sylow 2-Subgroups")

Pinned statement (verbatim from `tasks/gw-lemma29.md`, revised 2026-08-15 per
adversarial review revb: added `N ≠ ⊤` and `V ≤ S`).

The paper's `A := F₂'(N)` is the `2'`-part of the Fitting subgroup (p. 216:
`F_p(X) = O_p(F(X))`), formalized as
`K := oddCoreOf N ⊓ fittingSubgroupOf N`.  The D-group structure argument
first proves that `V` acts faithfully on `K`.  Coprime fixed-point generation
then supplies a second involution `v ∈ V` for which
`[⟨c.t⟩, C_K(v)] ≠ 1`.  After conjugating `v` to `c.t` and aligning the
image of `V` with the fixed Sylow subgroup inside `C_G(c.t)`, the local
`Lemma29Hypothesis` applies.  Transporting its two-core conclusion back to
`v` and applying the generalized 1.1(iv) centralization transfer contradicts
faithfulness.

Elimination status:
* `one_one_iv_transfer_bridge` — ELIMINATED (deleted): its statement is
  false without coprimality, and the landed, axiom-free
  `GorensteinWalter.centralizes_of_subnormal_selfCentralizing_coprime`
  (`GorensteinWalter.Section2.Lemma27Infra`) supplies the correct coprime
  transfer.  The bridge was unused by the assembled proof.
* `lemma_2_9_two_involution_bridge` — REPLACED.  The false fixed-`c.t`
  fixed-point bridge was removed.  The declaration now constructs the valid
  faithful-action pair `c.t, v` and its odd commutator subgroup.
* The conjugation/Sylow-alignment transport and the final centralization
  bridge are proved in this module; no theorem-local placeholder remains.
-/

namespace CFSG.GorensteinWalter

universe u

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

noncomputable section

/-- `O₂'(N)` has odd order. -/
private lemma oddCoreOf_odd_card {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) : Odd (Nat.card (↥(oddCoreOf N))) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have hcard : Nat.card (↥(oddCoreOf N)) ≠ 0 := (Nat.card_pos (α := ↥(oddCoreOf N))).ne'
  have h2dvd : 2 ∣ Nat.card (↥(oddCoreOf N)) := even_iff_two_dvd.mp heven
  have h2mem : 2 ∈ (Nat.card (↥(oddCoreOf N))).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2dvd, hcard⟩
  have h2mem' : 2 ∈ (Nat.card (↥(piCoreOf N ({q : ℕ | Odd q} : Set ℕ)))).primeFactors := by
    simpa [oddCoreOf_eq_piCoreOf_odd] using h2mem
  have hodd : Odd 2 := piCoreOf_primeDivisors N ({q : ℕ | Odd q} : Set ℕ) 2 h2mem'
  exact (by norm_num : ¬ Odd 2) hodd

private lemma central_inv_ne_one_dihedral {m : ℕ} (hm : 1 ≤ m) :
    DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ≠ 1 := by
  intro h
  have hinj : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0 := by
    apply DihedralGroup.r.inj
    rw [DihedralGroup.one_def] at h
    exact h
  have hval : (((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)).val = 0) :=
    (ZMod.val_eq_zero _).mpr hinj
  rw [ZMod.val_natCast] at hval
  have hdvd : 2 ^ m ∣ 2 ^ (m - 1) := Nat.dvd_iff_mod_eq_zero.mpr hval
  have hlt : 2 ^ (m - 1) < 2 ^ m :=
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : m - 1 < m)
  exact (not_lt_of_ge (Nat.le_of_dvd (pow_pos (by norm_num : 0 < 2) (m - 1)) hdvd)) hlt

private lemma central_inv_mem_center_dihedral {m : ℕ} (hm2 : 2 ≤ m) :
    DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ∈ Subgroup.center (DihedralGroup (2 ^ m)) := by
  rw [Subgroup.mem_center_iff]
  intro x
  rcases dihedralGroup_cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [DihedralGroup.r_mul_r, add_comm]
  · have hhalf : (2 : ZMod (2 ^ m)) * ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0 := by
      have htwo : (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) := by norm_num
      rw [htwo, ← Nat.cast_mul]
      have hpow : 2 * 2 ^ (m - 1) = 2 ^ m := by
        rw [mul_comm, ← pow_succ]
        congr 1
        omega
      rw [hpow]
      exact ZMod.natCast_self (2 ^ m)
    have hneg : -((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
      rw [neg_eq_iff_add_eq_zero]
      simpa [two_mul] using hhalf
    have hzcomm : DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) * DihedralGroup.sr i =
        DihedralGroup.sr i * DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
      rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
      apply congrArg DihedralGroup.sr
      rw [sub_eq_add_neg, hneg]
    exact hzcomm.symm

private lemma central_inv_mem_normal_subgroup_dihedral
    {m : ℕ} (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (D : Subgroup (DihedralGroup (2 ^ m))) (hDnormal : D.Normal) (hDne : D ≠ ⊥) :
    DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ∈ D := by
  classical
  rcases normal_subgroup_dihedral_two_pow hm D hDnormal with hrot | htop | hind
  · rcases hrot with ⟨k, hkle, hD⟩
    have hDbot : dihedralRotationSubgroup m m = ⊥ := by
      rw [dihedralRotationSubgroup_def]
      apply Subgroup.eq_bot_of_card_eq
      rw [Nat.card_zpowers]
      have hpowcast : (2 : ZMod (2 ^ m)) ^ m = ((2 ^ m : ℕ) : ZMod (2 ^ m)) :=
        (Nat.cast_pow (α := ZMod (2 ^ m)) 2 m).symm
      have hzero : ((2 ^ m : ℕ) : ZMod (2 ^ m)) = 0 := ZMod.natCast_self (2 ^ m)
      have hr0 : DihedralGroup.r ((2 ^ m : ℕ) : ZMod (2 ^ m)) = DihedralGroup.r 0 :=
        congrArg DihedralGroup.r hzero
      have hr1 : DihedralGroup.r ((2 ^ m : ℕ) : ZMod (2 ^ m)) = 1 := by
        rw [hr0, DihedralGroup.r_zero]
      have hord : orderOf (DihedralGroup.r (2 ^ m : ZMod (2 ^ m))) = 1 := by
        rw [orderOf_eq_one_iff]
        change DihedralGroup.r ((2 : ZMod (2 ^ m)) ^ m) = 1
        rw [hpowcast]
        exact hr1
      rw [hord]
    have hkne : k ≠ m := by
      intro hkm
      apply hDne
      rw [hD, hkm, hDbot]
    have hklt : k ≤ m - 1 := by omega
    let n : ℕ := 2 ^ (m - 1 - k)
    have hpow : (2 ^ (m - 1) : ℕ) = 2 ^ k * n := by
      dsimp [n]
      rw [← pow_add]
      congr 1
      omega
    have hcast : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) =
        ((2 ^ k : ℕ) : ZMod (2 ^ m)) * (n : ZMod (2 ^ m)) := by
      rw [← Nat.cast_mul, hpow]
    have hmem : DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ∈
        Subgroup.zpowers (DihedralGroup.r ((2 ^ k : ℕ) : ZMod (2 ^ m))) := by
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨n, ?_⟩
      rw [hcast]
      simpa [DihedralGroup.r_pow]
    rw [hD, dihedralRotationSubgroup_def]
    simpa using hmem
  · rw [htop]
    trivial
  · rcases hind with ⟨j, hD⟩
    rw [hD]
    have hzpow : DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ∈
        Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))) := by
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨2 ^ (m - 2), ?_⟩
      have hRp := DihedralGroup.r_pow (i := (2 : ZMod (2 ^ m))) (k := 2 ^ (m - 2))
      have hZeq : (2 : ZMod (2 ^ m)) * ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) =
          ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        have htwo : (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) := by norm_num
        rw [htwo, ← Nat.cast_mul]
        congr 1
        rw [mul_comm, ← pow_succ]
        congr 1
        omega
      exact hRp.trans (congrArg DihedralGroup.r hZeq)
    rw [mem_dihedralIndexTwoSubgroup_iff (by omega : 1 ≤ m) j]
    left
    rcases Subgroup.mem_zpowers_iff.mp hzpow with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc
      DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) =
          DihedralGroup.r (2 : ZMod (2 ^ m)) ^ k := hk.symm
      _ = DihedralGroup.r
          ((2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m))) :=
        DihedralGroup.r_zpow (i := (2 : ZMod (2 ^ m))) (k := k)

private lemma normal_subgroup_dihedral_mulEquiv_inter_kleinFour_ne_bot
    {K : Type u} [Group K] [Finite K] {m : ℕ} (hm : 1 ≤ m)
    (e : K ≃* DihedralGroup (2 ^ m))
    (D V : Subgroup K) (hDnormal : D.Normal) (hDne : D ≠ ⊥)
    (hV : IsKleinFour V) :
    D ⊓ V ≠ ⊥ := by
  classical
  by_cases hm2 : 2 ≤ m
  · let z : K := e.symm (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    have hzcenter : z ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply e.injective
      have hz : e z = DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        simp [z]
      rw [map_mul, map_mul, hz]
      exact (Subgroup.mem_center_iff.mp (central_inv_mem_center_dihedral hm2) (e y))
    have hzV : z ∈ V := center_mem_kleinFour_of_dihedral_mulEquiv hm e V hV hzcenter
    let D' : Subgroup (DihedralGroup (2 ^ m)) := D.map e.toMonoidHom
    have hD'normal : D'.Normal := by
      exact (e.normal_map_iff).2 hDnormal
    have hD'ne : D' ≠ ⊥ := by
      intro hbot
      apply hDne
      exact (Subgroup.map_eq_bot_iff_of_injective D (f := e.toMonoidHom) e.injective).mp hbot
    have hzD' : e z ∈ D' := by
      simpa [z, D'] using
        (central_inv_mem_normal_subgroup_dihedral hm hm2 D' hD'normal hD'ne)
    have hzD : z ∈ D := by
      rw [Subgroup.mem_map] at hzD'
      rcases hzD' with ⟨y, hyD, hye⟩
      have hyz : y = z := e.injective hye
      simpa [hyz] using hyD
    have hz_ne : z ≠ 1 := by
      intro hz1
      apply central_inv_ne_one_dihedral hm
      have hze : e z = e 1 := congrArg e hz1
      simpa [z] using hze
    intro hbot
    apply hz_ne
    have hmem : z ∈ D ⊓ V := ⟨hzD, hzV⟩
    have hzbot : z ∈ (⊥ : Subgroup K) := by
      rw [hbot] at hmem
      exact hmem
    exact Subgroup.mem_bot.mp hzbot
  · have hm1 : m = 1 := by omega
    have hKcard : Nat.card K = 4 := by
      have hc := Nat.card_congr e.toEquiv
      rw [DihedralGroup.nat_card] at hc
      simpa [hm1] using hc
    have hVtop : V = ⊤ := by
      apply Subgroup.eq_top_of_card_eq V
      rw [IsKleinFour.card_four (G := V), hKcard]
    intro hbot
    apply hDne
    have hDV : D ⊓ V = D := by
      rw [hVtop, inf_top_eq]
    rw [hDV] at hbot
    exact hbot

private lemma twoCoreOf_isNormalIn {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) : IsNormalIn (twoCoreOf N) N := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, hfx⟩
    rw [← hfx]
    change (f : G) ∈ N
    simp
  · intro h hh k hk
    rcases (Subgroup.mem_map).1 hk with ⟨f, hf, hfk⟩
    rw [← hfk]
    have hconj : (⟨h, hh⟩ : ↥N) * f * (⟨h, hh⟩ : ↥N)⁻¹ ∈ pCore 2 N :=
      (pCore_normal (G := N)).conj_mem (n := f) hf (g := ⟨h, hh⟩)
    refine Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : ↥N) * f * (⟨h, hh⟩ : ↥N)⁻¹, hconj, ?_⟩
    rw [hfk]
    simpa using hfk

private lemma hasCyclicOrDihedralSylowTwo_of_isDGroup {G : Type u} [Group G] [Finite G]
    (hD : IsDGroup G) : HasCyclicOrDihedralSylowTwo G := by
  rcases hD with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _, _, _, _, _, _⟩
  · exact h
  · exact h
  · exact h

private lemma exists_dihedralSylow_subgroup_of_kleinFour
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (N V : Subgroup G)
    (hNtop : N ≠ ⊤) (hV : IsKleinFour V) (hVN : V ≤ N) :
    ∃ (T' : Sylow 2 N),
      V ≤ (T' : Subgroup N).map N.subtype ∧
        ∃ m : ℕ, 1 ≤ m ∧
          Nonempty (((T' : Subgroup N).map N.subtype) ≃* DihedralGroup (2 ^ m)) := by
  classical
  have hD : IsDGroup N := properSubgroups_areDGroups hmin N hNtop
  have hSylow : HasCyclicOrDihedralSylowTwo N := hasCyclicOrDihedralSylowTwo_of_isDGroup hD
  let V' : Subgroup N := V.subgroupOf N
  have eVV : V' ≃* V := Subgroup.subgroupOfEquivOfLe hVN
  have hV' : IsKleinFour V' := {
    card_four := (Nat.card_congr eVV.toEquiv).trans hV.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eVV).trans hV.exponent_two
  }
  have hV'p : IsPGroup 2 V' := by
    refine (IsPGroup.iff_card (p := 2) (G := V')).2 ?_
    refine ⟨2, ?_⟩
    rw [Nat.card_congr eVV.toEquiv]
    exact hV.card_four
  obtain ⟨T', hV'T'⟩ := IsPGroup.exists_le_sylow (G := N) hV'p
  have hT'notcyc : ¬ IsCyclic T' := by
    intro hcyc
    have : IsCyclic T' := hcyc
    have hV'cyc : IsCyclic V' := Subgroup.isCyclic_of_le hV'T'
    exact IsKleinFour.not_isCyclic (G := V') hV'cyc
  have hT'dih := (hSylow T').resolve_left hT'notcyc
  rcases hT'dih with ⟨m, hm, eT'⟩
  let T : Subgroup G := (T' : Subgroup N).map N.subtype
  have hTleN : T ≤ N := Subgroup.map_subtype_le (H := N) (T' : Subgroup N)
  have hVleT : V ≤ T := by
    have hmap : V'.map N.subtype ≤ T :=
      Subgroup.map_mono (f := N.subtype) hV'T'
    simpa [V', T, Subgroup.map_subgroupOf_eq_of_le hVN] using hmap
  have eT : Nonempty (T ≃* DihedralGroup (2 ^ m)) := by
    have eTT' : T ≃* T' := by
      simpa [T] using (Subgroup.equivMapOfInjective (T' : Subgroup N) N.subtype N.subtype_injective).symm
    exact ⟨eTT'.trans eT'.some⟩
  exact ⟨T', hVleT, m, hm, eT⟩

public theorem twoCoreOf_eq_bot_of_kleinFour_hV2
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (N V : Subgroup G)
    (hNtop : N ≠ ⊤) (hV : IsKleinFour V) (hVN : V ≤ N)
    (hV2 : V ⊓ twoCoreOf N = ⊥) : twoCoreOf N = ⊥ := by
  classical
  by_contra hO
  rcases exists_dihedralSylow_subgroup_of_kleinFour hmin N V hNtop hV hVN with
    ⟨T', hVleT, m, hm, eT⟩
  let T : Subgroup G := (T' : Subgroup N).map N.subtype
  have hOleN : twoCoreOf N ≤ N := by
    exact Subgroup.map_subtype_le (H := N) (pCore 2 N)
  let O' : Subgroup N := (twoCoreOf N).subgroupOf N
  have hO'normal : O'.Normal := by
    have hnorm : IsNormalIn (twoCoreOf N) N := twoCoreOf_isNormalIn N
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := N) (N := twoCoreOf N)
      (le_normalizer_of_isNormalIn hnorm)
  have hO'p : IsPGroup 2 O' := by
    have hOp : IsPGroup 2 (twoCoreOf N) := by
      rw [twoCoreOf]
      exact IsPGroup.map (pCore_isPGroup (G := N) (p := 2)) N.subtype
    have e : O' ≃* twoCoreOf N := Subgroup.subgroupOfEquivOfLe hOleN
    exact hOp.of_equiv e.symm
  have hO'leT' : O' ≤ (T' : Subgroup N) :=
    IsPGroup.le_sylow_of_normal (p := 2) (G := N) hO'p T'
  have hOleT : twoCoreOf N ≤ T := by
    have hmap : O'.map N.subtype ≤ T := Subgroup.map_mono (f := N.subtype) hO'leT'
    simpa [T, O', Subgroup.map_subgroupOf_eq_of_le hOleN] using hmap
  let D : Subgroup T := (twoCoreOf N).subgroupOf T
  let VK : Subgroup T := V.subgroupOf T
  have hDne : D ≠ ⊥ := by
    intro hbot
    apply hO
    have hmap : D.map T.subtype = twoCoreOf N :=
      Subgroup.map_subgroupOf_eq_of_le hOleT
    have hmapbot : D.map T.subtype = ⊥ := by
      rw [hbot, Subgroup.map_bot]
    rw [← hmap]
    exact hmapbot
  have hDnormal : D.Normal := by
    have hnorm : IsNormalIn (twoCoreOf N) N := twoCoreOf_isNormalIn N
    have hTleN : T ≤ N := Subgroup.map_subtype_le (H := N) (T' : Subgroup N)
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := T) (N := twoCoreOf N)
      (hTleN.trans (le_normalizer_of_isNormalIn hnorm))
  have hVK : IsKleinFour VK := by
    have e : VK ≃* V := Subgroup.subgroupOfEquivOfLe hVleT
    refine {
      card_four := (Nat.card_congr e.toEquiv).trans hV.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv e).trans hV.exponent_two
    }
  have hDinter : D ⊓ VK ≠ ⊥ :=
    normal_subgroup_dihedral_mulEquiv_inter_kleinFour_ne_bot hm eT.some D VK hDnormal hDne hVK
  have hOV : (twoCoreOf N) ⊓ V ≠ ⊥ := by
    intro hbot
    apply hDinter
    apply le_bot_iff.mp
    intro x hx
    have hxO : (x : G) ∈ twoCoreOf N := (Subgroup.mem_subgroupOf).mp hx.1
    have hxV : (x : G) ∈ V := (Subgroup.mem_subgroupOf).mp hx.2
    have hxOV : (x : G) ∈ (twoCoreOf N) ⊓ V := ⟨hxO, hxV⟩
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [hbot] at hxOV
      exact hxOV
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hxbot
  have hV2' : V ⊓ twoCoreOf N ≠ ⊥ := by simpa [inf_comm] using hOV
  exact hV2' hV2

private lemma isQuasisimple_even_card {Q : Type u} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) : 2 ∣ Nat.card Q := by
  classical
  have : Nontrivial Q := hQ.1
  have : Group.IsPerfect Q := (Group.isPerfect_def).2 hQ.2.1
  by_contra hnot
  have hodd : Odd (Nat.card Q) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact hnot (even_iff_two_dvd.mp heven)
  have hsolv : IsSolvable Q := odd_order_theorem Q hodd
  exact Group.IsPerfect.not_isSolvable Q hsolv

private lemma isQuasisimple_mulEquiv_local
    {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (hG : IsQuasisimple G) :
    IsQuasisimple H := by
  have hNontriv : Nontrivial H := by
    let : Nontrivial G := hG.1
    exact e.toEquiv.injective.nontrivial
  have hPerf : Group.IsPerfect H := by
    let : Group.IsPerfect G := (Group.isPerfect_def).2 hG.2.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.toEquiv.surjective
  have hSimple : IsSimpleGroup (H ⧸ Subgroup.center H) := by
    have he : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
      apply le_antisymm
      · intro x hx
        rcases hx with ⟨y, hy, rfl⟩
        exact (Subgroup.centerCongr e ⟨y, hy⟩).2
      · intro x hx
        refine ⟨e.symm x, ?_, ?_⟩
        · exact ((Subgroup.centerCongr e).symm ⟨x, hx⟩).2
        · exact e.apply_symm_apply x
    exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e he)).mp hG.2.2
  exact ⟨hNontriv, (Group.isPerfect_def).1 hPerf, hSimple⟩

private lemma isSubnormal_of_isComponentOf_top_local
    {G : Type u} [Group G] {K : Subgroup G}
    (hK : IsComponentOf K (⊤ : Subgroup G)) :
    K.IsSubnormal := by
  have h' : ((K.subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype).IsSubnormal :=
    hK.2.1.map (f := (⊤ : Subgroup G).subtype)
      (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
  rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : K ≤ (⊤ : Subgroup G))] at h'

private lemma isComponentOf_of_isComponentOf_top_map_local
    {G : Type u} [Group G] {B : Subgroup G} {E : Subgroup (↥B)}
    (hE : IsComponentOf E (⊤ : Subgroup (↥B))) :
    IsComponentOf (E.map B.subtype) B := by
  refine ⟨Subgroup.map_subtype_le E, ?_, ?_⟩
  · have hEsub : E.IsSubnormal := isSubnormal_of_isComponentOf_top_local hE
    have hEq : (E.map B.subtype).subgroupOf B = E := by
      apply le_antisymm
      · intro y hy
        rw [Subgroup.mem_subgroupOf] at hy
        rcases (Subgroup.mem_map).1 hy with ⟨x, hx, hxy⟩
        have hyx : x = y := B.subtype_injective (by simpa using hxy)
        simpa [hyx] using hx
      · intro y hy
        rw [Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_map).mpr ⟨y, hy, rfl⟩
    simpa [hEq] using hEsub
  · exact isQuasisimple_mulEquiv_local
      (Subgroup.equivMapOfInjective E B.subtype B.subtype_injective) hE.2.2

private lemma isComponentOf_of_isComponentOf_subgroup_local
    {G : Type u} [Group G] {A E : Subgroup G} (hE : IsComponentOf E A) :
    IsComponentOf (E.subgroupOf A) (⊤ : Subgroup (↥A)) :=
  ⟨le_top, hE.2.1.subgroupOf,
    isQuasisimple_mulEquiv_local (Subgroup.subgroupOfEquivOfLe hE.1).symm hE.2.2⟩

private lemma componentLayer_top_map_eq_componentLayerOf_local
    {G : Type u} [Group G] (B : Subgroup G) :
    (componentLayerOf (⊤ : Subgroup (↥B))).map B.subtype = componentLayerOf B := by
  apply le_antisymm
  · refine (Subgroup.map_le_iff_le_comap).2 ?_
    change sSup {E : Subgroup (↥B) | IsComponentOf E (⊤ : Subgroup (↥B))} ≤
      Subgroup.comap B.subtype (componentLayerOf B)
    refine sSup_le ?_
    intro E hE
    intro y hy
    rw [Subgroup.mem_comap]
    exact le_sSup (s := {E' : Subgroup G | IsComponentOf E' B})
      (a := E.map B.subtype)
      (isComponentOf_of_isComponentOf_top_map_local hE)
      (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
  · change sSup {E : Subgroup G | IsComponentOf E B} ≤
      Subgroup.map B.subtype
        (sSup {E : Subgroup (↥B) | IsComponentOf E (⊤ : Subgroup (↥B))})
    refine sSup_le ?_
    intro E hE
    intro y hy
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hE.1 hy⟩,
        Subgroup.mem_sSup_of_mem
          (isComponentOf_of_isComponentOf_subgroup_local hE)
          (by
            rw [Subgroup.mem_subgroupOf]
            exact hy),
        rfl⟩

private lemma componentLayerOf_top_eq_bot_of_componentLayerOf_bot
    {G : Type u} [Group G] [Finite G] (N : Subgroup G)
    (hE : componentLayerOf N = ⊥) :
    componentLayerOf (⊤ : Subgroup (↥N)) = ⊥ := by
  have hmap : (componentLayerOf (⊤ : Subgroup (↥N))).map N.subtype = componentLayerOf N :=
    componentLayer_top_map_eq_componentLayerOf_local N
  apply (Subgroup.map_eq_bot_iff_of_injective (componentLayerOf (⊤ : Subgroup (↥N)))
    (f := N.subtype) N.subtype_injective).1
  rw [hmap, hE]

private lemma componentLayerOf_ne_bot_iff {G : Type u} [Group G]
    (N : Subgroup G) :
    componentLayerOf N ≠ ⊥ ↔ ∃ S : Subgroup G, IsComponentOf S N ∧ S ≠ ⊥ := by
  constructor
  · intro hE
    by_contra hnone
    push Not at hnone
    apply hE
    apply le_bot_iff.mp
    rw [componentLayerOf]
    refine sSup_le ?_
    intro S hS
    have hSbot : S = ⊥ := hnone S hS
    simpa [hSbot]
  · rintro ⟨S, hS, hSne⟩ hbot
    have hSle : S ≤ componentLayerOf N := le_sSup hS
    have hSbot' : S = ⊥ := le_bot_iff.mp (hSle.trans (le_of_eq hbot))
    exact hSne hSbot'

private lemma componentLayerOf_exists_sylow_two_ne_bot
    {G : Type u} [Group G] [Finite G] (N : Subgroup G)
    (hE : componentLayerOf N ≠ ⊥) :
    ∃ P : Sylow 2 (↥(componentLayerOf N)), (P : Subgroup (componentLayerOf N)) ≠ ⊥ := by
  classical
  let E : Subgroup G := componentLayerOf N
  rcases (componentLayerOf_ne_bot_iff N).1 hE with ⟨S, hS, hSne⟩
  let S_E : Subgroup E := S.subgroupOf E
  have hSE : S ≤ E := le_sSup hS
  have eSE : S_E ≃* S := Subgroup.subgroupOfEquivOfLe hSE
  have hSq : IsQuasisimple S_E := by
    exact isQuasisimple_mulEquiv_local (Subgroup.subgroupOfEquivOfLe hSE).symm hS.2.2
  have hSeven : 2 ∣ Nat.card S_E := isQuasisimple_even_card hSq
  have hEdvd : 2 ∣ Nat.card E := by
    have hdvd : Nat.card S_E ∣ Nat.card E :=
      Subgroup.card_subgroup_dvd_card (α := ↥E) S_E
    exact hSeven.trans hdvd
  let P : Sylow 2 E := Classical.choice Sylow.nonempty
  exact ⟨P, Sylow.ne_bot_of_dvd_card (G := E) P hEdvd⟩

private lemma coe_smul_eq_conjBy {G : Type*} [Group G] (TP : Sylow 2 G) (h : G) :
    ((h • TP : Sylow 2 G) : Subgroup G) = (TP : Subgroup G).conjBy h := by
  ext x
  change x ∈ (MulAut.conj h • ((TP : Subgroup G) : Set G) : Set G) ↔ x ∈ (TP : Subgroup G).conjBy h
  rw [Set.mem_smul_set]
  exact Iff.rfl

private lemma componentLayerOf_eq_bot_of_kleinFour_hVE
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (N V : Subgroup G)
    (hNtop : N ≠ ⊤) (hV : IsKleinFour V) (hVN : V ≤ N)
    (hVE : V ⊓ componentLayerOf N = ⊥) : componentLayerOf N = ⊥ := by
  classical
  by_contra hE
  let E : Subgroup G := componentLayerOf N
  obtain ⟨P_E, hP_Ene⟩ := componentLayerOf_exists_sylow_two_ne_bot N hE
  let P_G : Subgroup G := (P_E : Subgroup E).map E.subtype
  have hPp : IsPGroup 2 P_G := by
    exact IsPGroup.map (P_E.isPGroup') E.subtype
  have hPne : P_G ≠ ⊥ := by
    intro hbot
    apply hP_Ene
    exact (Subgroup.map_eq_bot_iff_of_injective (P_E : Subgroup E) (f := E.subtype)
      E.subtype_injective).mp hbot
  have hE_le_N : E ≤ N := by
    change componentLayerOf N ≤ N
    rw [componentLayerOf]
    refine sSup_le ?_
    intro S hS
    exact hS.1
  have hPleE : P_G ≤ E := Subgroup.map_subtype_le (H := E) (P_E : Subgroup E)
  have hPleN : P_G ≤ N := by
    exact hPleE.trans hE_le_N
  let P_N : Subgroup N := P_G.subgroupOf N
  have hPneN : P_N ≠ ⊥ := by
    intro hbot
    apply hPne
    have hmap : P_N.map N.subtype = P_G := Subgroup.map_subgroupOf_eq_of_le hPleN
    rw [← hmap]
    exact (Subgroup.map_eq_bot_iff_of_injective P_N (f := N.subtype) N.subtype_injective).mpr hbot
  have hPpN : IsPGroup 2 P_N := by
    have e : P_N ≃* P_G := Subgroup.subgroupOfEquivOfLe hPleN
    exact hPp.of_equiv e.symm
  obtain ⟨T0, hPleT0⟩ := IsPGroup.exists_le_sylow (G := N) hPpN
  rcases exists_dihedralSylow_subgroup_of_kleinFour hmin N V hNtop hV hVN with
    ⟨T', hVleT, m, hm, eT⟩
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq N T0 T'
  let P_Nh : Subgroup N := P_N.conjBy h
  have hP_Nh_le_T' : P_Nh ≤ (T' : Subgroup N) := by
    have hle1 : P_Nh ≤ ↑(h • T0 : Sylow 2 N) := by
      rw [coe_smul_eq_conjBy]
      exact Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hPleT0
    rwa [hh] at hle1
  let E' : Subgroup N := E.subgroupOf N
  have hE'normal : E'.Normal := by
    have hnorm : IsNormalIn E N := componentLayerOf_isNormalIn N
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := N) (N := E)
      (le_normalizer_of_isNormalIn hnorm)
  have hPleE' : P_N ≤ E' := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hPleE ((Subgroup.mem_subgroupOf).mp hx)
  have hP_Nh_le_E' : P_Nh ≤ E' := by
    intro x hx
    rcases (Subgroup.mem_map).mp hx with ⟨y, hyP, hxy⟩
    have hyE : y ∈ E' := hPleE' hyP
    have hconjE : (h : N) * y * (h : N)⁻¹ ∈ E' :=
      Subgroup.Normal.conj_mem hE'normal y hyE h
    have hxeq : x = h * y * h⁻¹ := by
      simpa [MulAut.conj_apply] using hxy.symm
    rw [hxeq]
    exact hconjE
  have hP_Nh_ne : P_Nh ≠ ⊥ := by
    intro hbot
    apply hPneN
    exact (Subgroup.map_eq_bot_iff_of_injective P_N (f := (MulAut.conj h).toMonoidHom)
      (MulAut.conj h).injective).mp hbot
  let T_G : Subgroup G := (T' : Subgroup N).map N.subtype
  let D_amb : Subgroup G := T_G ⊓ E
  have hP_Nh_amb_le_D : P_Nh.map N.subtype ≤ D_amb := by
    intro x hx
    rcases (Subgroup.mem_map).mp hx with ⟨y, hy, rfl⟩
    have hyT : (y : G) ∈ T_G := by
      exact Subgroup.mem_map.mpr ⟨y, hP_Nh_le_T' hy, rfl⟩
    have hyE : (y : G) ∈ E := by
      have hyE' : y ∈ E' := hP_Nh_le_E' hy
      exact (Subgroup.mem_subgroupOf).mp hyE'
    exact ⟨hyT, hyE⟩
  have hD_amb_ne : D_amb ≠ ⊥ := by
    intro hbot
    apply hP_Nh_ne
    have hmapbot : P_Nh.map N.subtype = ⊥ := by
      apply le_bot_iff.mp
      intro y hy
      have hyD : y ∈ D_amb := hP_Nh_amb_le_D hy
      rw [hbot] at hyD
      exact hyD
    exact (Subgroup.map_eq_bot_iff_of_injective P_Nh (f := N.subtype)
      N.subtype_injective).mp hmapbot
  let D_K : Subgroup T_G := D_amb.subgroupOf T_G
  have hD_Kne : D_K ≠ ⊥ := by
    intro hbot
    apply hD_amb_ne
    have hmap : D_K.map T_G.subtype = D_amb :=
      Subgroup.map_subgroupOf_eq_of_le (inf_le_left : D_amb ≤ T_G)
    rw [← hmap]
    exact (Subgroup.map_eq_bot_iff_of_injective D_K (f := T_G.subtype)
      T_G.subtype_injective).mpr hbot
  have hD_Knormal : D_K.Normal := by
    have hDnorm : IsNormalIn D_amb T_G := by
      refine ⟨?_, ?_⟩
      · intro x hx
        exact hx.1
      · intro t ht x hx
        have htN : (t : G) ∈ N := by
          rcases (Subgroup.mem_map).mp ht with ⟨x, hx, rfl⟩
          exact x.2
        refine ⟨?_, ?_⟩
        · exact Subgroup.mul_mem (T_G) (Subgroup.mul_mem T_G ht hx.1) (T_G.inv_mem ht)
        · exact (componentLayerOf_isNormalIn N).2 (t : G) htN (x : G) hx.2
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := T_G) (N := D_amb)
      (le_normalizer_of_isNormalIn hDnorm)
  have hVleT_G : V ≤ T_G := by
    simpa [T_G] using hVleT
  let VK : Subgroup T_G := V.subgroupOf T_G
  have hVK : IsKleinFour VK := by
    have e : VK ≃* V := Subgroup.subgroupOfEquivOfLe hVleT_G
    refine {
      card_four := (Nat.card_congr e.toEquiv).trans hV.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv e).trans hV.exponent_two
    }
  have hDinter : D_K ⊓ VK ≠ ⊥ :=
    normal_subgroup_dihedral_mulEquiv_inter_kleinFour_ne_bot hm eT.some D_K VK hD_Knormal hD_Kne hVK
  have hEV : E ⊓ V ≠ ⊥ := by
    intro hbot
    apply hDinter
    apply le_bot_iff.mp
    intro x hx
    have hxD : (x : G) ∈ D_amb := (Subgroup.mem_subgroupOf).mp hx.1
    have hxE : (x : G) ∈ E := hxD.2
    have hxV : (x : G) ∈ V := (Subgroup.mem_subgroupOf).mp hx.2
    have hxEV : (x : G) ∈ E ⊓ V := ⟨hxE, hxV⟩
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [hbot] at hxEV
      exact hxEV
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hxbot
  have hVE' : V ⊓ E ≠ ⊥ := by simpa [inf_comm] using hEV
  exact hVE' hVE

private lemma fittingSubgroupOf_le_oddCore_of_twoCore_bot
    {G : Type u} [Group G] [Finite G] (N : Subgroup G)
    (hO2 : twoCoreOf N = ⊥) : fittingSubgroupOf N ≤ oddCoreOf N := by
  classical
  have hpcore : pCore 2 N = ⊥ := by
    exact (Subgroup.map_eq_bot_iff_of_injective (pCore 2 N) (f := N.subtype)
      N.subtype_injective).1 (by simpa [twoCoreOf] using hO2)
  have hle : fittingSubgroup N ≤ pCore 2 N ⊔ pPrimeCore 2 N :=
    section9_fitting_le_pCore_sup_pPrimeCore (G := N) (p := 2)
  have hle' : fittingSubgroup N ≤ pPrimeCore 2 N := by
    rw [hpcore, bot_sup_eq] at hle
    exact hle
  have hmap := Subgroup.map_mono (f := N.subtype) hle'
  simpa [fittingSubgroupOf, oddCoreOf] using hmap

private lemma mem_fittingSubgroup_of_mem_fittingSubgroupOf
    {G : Type u} [Group G] [Finite G] (N : Subgroup G) {x : ↥N}
    (hx : (x : G) ∈ fittingSubgroupOf N) : x ∈ fittingSubgroup N := by
  rcases (Subgroup.mem_map).mp hx with ⟨y, hyF, hyx⟩
  have hyx' : y = x := N.subtype_injective hyx
  simpa [hyx'] using hyF

private lemma map_fittingSubgroup_le_of_surjective_local
    {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) :
    (fittingSubgroup G).map f ≤ fittingSubgroup H := by
  have hmap_normal : ((fittingSubgroup G).map f).Normal :=
    Subgroup.Normal.map (H := fittingSubgroup G) inferInstance f hf
  have hmap_nil : Group.IsNilpotent ↥((fittingSubgroup G).map f) := by
    have : Group.IsNilpotent ↥(fittingSubgroup G) := by infer_instance
    let ψ : fittingSubgroup G →* ↥((fittingSubgroup G).map f) :=
      { toFun := fun g => ⟨f g, Subgroup.mem_map.mpr ⟨g.1, g.2, rfl⟩⟩
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp [map_mul] }
    have hψsurj : Function.Surjective ψ := by
      intro x
      rcases (Subgroup.mem_map).1 x.2 with ⟨g, hg, hx⟩
      refine ⟨⟨g, hg⟩, ?_⟩
      apply Subtype.ext
      exact hx
    exact Group.nilpotent_of_surjective ψ hψsurj
  exact le_sSup ⟨hmap_normal, hmap_nil⟩

private lemma map_fittingSubgroup_of_mulEquiv_local
    {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) :
    (fittingSubgroup G).map e.toMonoidHom = fittingSubgroup H := by
  apply le_antisymm
  · exact map_fittingSubgroup_le_of_surjective_local e.toMonoidHom e.surjective
  · have hback : (fittingSubgroup H).map e.symm.toMonoidHom ≤ fittingSubgroup G :=
      map_fittingSubgroup_le_of_surjective_local e.symm.toMonoidHom e.symm.surjective
    have hmap : ((fittingSubgroup H).map e.symm.toMonoidHom).map e.toMonoidHom ≤
        (fittingSubgroup G).map e.toMonoidHom :=
      Subgroup.map_mono (f := e.toMonoidHom) hback
    have hleft : ((fittingSubgroup H).map e.symm.toMonoidHom).map e.toMonoidHom =
        fittingSubgroup H := by
      rw [Subgroup.map_map]
      have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
        ext x
        simp
      rw [hcomp, Subgroup.map_id]
    rw [hleft] at hmap
    exact hmap

private lemma map_generalizedFittingSubgroupOf_top_subtype_local
    {G : Type u} [Group G] [Finite G] (B : Subgroup G) :
    (generalizedFittingSubgroupOf (⊤ : Subgroup (↥B))).map B.subtype =
      generalizedFittingSubgroupOf B := by
  rw [generalizedFittingSubgroupOf, generalizedFittingSubgroupOf, Subgroup.map_sup]
  rw [componentLayer_top_map_eq_componentLayerOf_local B]
  have : Finite (↥(⊤ : Subgroup (↥B))) :=
    Finite.of_equiv (↥B) (Subgroup.topEquiv (G := ↥B)).toEquiv.symm
  change Subgroup.map B.subtype ((fittingSubgroup (↥(⊤ : Subgroup (↥B)))).map
      (⊤ : Subgroup (↥B)).subtype) ⊔ componentLayerOf B =
    Subgroup.map B.subtype (fittingSubgroup (↥B)) ⊔ componentLayerOf B
  have hTopSubtype :
      (⊤ : Subgroup (↥B)).subtype =
        (Subgroup.topEquiv (G := ↥B)).toMonoidHom := by
    ext x
    rfl
  rw [hTopSubtype]
  rw [map_fittingSubgroup_of_mulEquiv_local (Subgroup.topEquiv (G := ↥B))]

private lemma centralizer_intersection_fstar_le_fstar_local
    {G : Type u} [Group G] [Finite G] (B : Subgroup G) :
    Subgroup.centralizer ((generalizedFittingSubgroupOf B : Set G)) ⊓ B ≤
      generalizedFittingSubgroupOf B := by
  let Y : Subgroup (↥B) := generalizedFittingSubgroupOf (⊤ : Subgroup (↥B))
  have hYcent : Subgroup.centralizer (Y : Set (↥B)) ≤ Y :=
    fstar_self_centralizing (G := ↥B)
  have hmap : Y.map B.subtype = generalizedFittingSubgroupOf B :=
    map_generalizedFittingSubgroupOf_top_subtype_local B
  intro x hx
  rcases hx with ⟨hxC, hxB⟩
  let b : ↥B := ⟨x, hxB⟩
  have hbC : b ∈ Subgroup.centralizer (Y : Set (↥B)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hy' : (y : G) ∈ generalizedFittingSubgroupOf B := by
      rw [← hmap]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp hxC (y : G) hy')
  have hbY : b ∈ Y := hYcent hbC
  rw [← hmap]
  exact Subgroup.mem_map.mpr ⟨b, hbY, rfl⟩



/-- **Eliminating bridge** (D-group structure, re-pinned 2026-08-16 around
`K = F₂'(N) := O₂'(N) ∩ F(N)` with the actual use-site hypotheses `hV2` and
`hVE`).  The paper's dihedral-paper 1.6 (case analysis) gives one of four
cases: (a) `C_N(F₂'(N)) ≤ F₂'(N)`; (b) a central involution; (c) `O₂(N)`
Klein four; (d) a normal quasisimple subgroup `E` with solvable quotient.
With `hV2`/`hVE`:

* case (b): the central involution lies in `O₂(N)` and in every Klein four
  of the Sylow `2`-subgroup, contradicting `hV2`;
* case (c): `O₂(N) ≤ T` meets `V` in the central involution, again
  contradicting `hV2`;
* case (d): the Sylow `2`-subgroup `T ∩ E` contains the central involution
  of `T`, which also lies in `V`, contradicting `hVE`.

Only case (a) survives, and then `K₀ ≤ V ∩ F₂'(N) = ⊥` (a `2`-subgroup of
the odd group `F₂'(N)`), so the conclusion is trivial.  The order-300
`(C₅×C₅)⋊C₃⋊V₄` GAP example does **not** refute this statement: its
`C_N(F₂'(N)) = F₂'(N) = C₅×C₅` satisfies 1.6(a), and no nonidentity element
of `V` centralizes `F₂'(N)`.  That example remains relevant only as a
counterexample to the abandoned full-odd-core/subnormality route.

Elimination: formalize dihedral-paper 1.6's four cases for
`IsDGroup N` (`properSubgroups_areDGroups hmin N hNtop`) and the Sylow
alignment/central-involution facts for a Klein-four `V`. -/
private theorem dGroup_centralizer_f2p_twoSubgroup_le_twoCore_or_layer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (N V : Subgroup G)
    (hNtop : N ≠ ⊤) (hV : IsKleinFour V) (hVN : V ≤ N)
    (hV2 : V ⊓ twoCoreOf N = ⊥) (hVE : V ⊓ componentLayerOf N = ⊥)
    {K₀ : Subgroup G} (hK₀V : K₀ ≤ V)
    (hK₀C : K₀ ≤ Subgroup.centralizer
      (oddCoreOf N ⊓ fittingSubgroupOf N : Set G)) :
    K₀ ≤ twoCoreOf N ∨ K₀ ≤ componentLayerOf N := by
  classical
  have hO2 : twoCoreOf N = ⊥ :=
    twoCoreOf_eq_bot_of_kleinFour_hV2 hmin N V hNtop hV hVN hV2
  have hE : componentLayerOf N = ⊥ :=
    componentLayerOf_eq_bot_of_kleinFour_hVE hmin N V hNtop hV hVN hVE
  let A : Subgroup G := oddCoreOf N ⊓ fittingSubgroupOf N
  have hFleA : fittingSubgroupOf N ≤ A :=
    le_inf (fittingSubgroupOf_le_oddCore_of_twoCore_bot N hO2) le_rfl
  have hAeqF : A = fittingSubgroupOf N := le_antisymm inf_le_right hFleA
  have hFstarN : generalizedFittingSubgroupOf N = A := by
    rw [generalizedFittingSubgroupOf, hE, sup_bot_eq, hAeqF]
  have hselfN :
      Subgroup.centralizer ((generalizedFittingSubgroupOf N : Set G)) ⊓ N ≤
        generalizedFittingSubgroupOf N :=
    centralizer_intersection_fstar_le_fstar_local N
  have hKleA : K₀ ≤ A := by
    intro k hk
    have hkN : k ∈ N := hVN (hK₀V hk)
    have hkC : k ∈ Subgroup.centralizer ((generalizedFittingSubgroupOf N : Set G)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haA : a ∈ A := by
        rw [← hFstarN]
        exact ha
      exact (Subgroup.mem_centralizer_iff.mp (hK₀C hk) a haA)
    have hkCinter : k ∈ Subgroup.centralizer ((generalizedFittingSubgroupOf N : Set G)) ⊓ N :=
      ⟨hkC, hkN⟩
    have hkF : k ∈ generalizedFittingSubgroupOf N := hselfN hkCinter
    rw [← hFstarN]
    exact hkF
  have hAodd : Nat.Coprime 2 (Nat.card A) := by
    have hcopA : Nat.Coprime 2 (Nat.card (oddCoreOf N)) :=
      Nat.coprime_two_left.mpr (oddCoreOf_odd_card N)
    have hdvd : Nat.card A ∣ Nat.card (oddCoreOf N) := by
      have hKA : A ≤ oddCoreOf N := inf_le_left
      have hcard : Nat.card A = Nat.card (A.subgroupOf (oddCoreOf N)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv.symm
      rw [hcard]
      exact (A.subgroupOf (oddCoreOf N)).card_subgroup_dvd_card
    exact Nat.Coprime.of_dvd_right hdvd hcopA
  have hAVbot : A ⊓ V = ⊥ := by
    have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by
      rw [hV.card_four]
      exact hAodd.symm.pow_right 2
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  have hKbot : K₀ = ⊥ := by
    apply le_bot_iff.mp
    intro k hk
    have hkV : k ∈ V := hK₀V hk
    have hkA : k ∈ A := hKleA hk
    have hkAV : k ∈ A ⊓ V := ⟨hkA, hkV⟩
    have hkbot : k ∈ (⊥ : Subgroup G) := by
      rw [hAVbot] at hkAV
      exact hkAV
    exact hkbot
  left
  rw [hO2, hKbot]


/-- Faithfulness of the Klein-four `V` on `K = F₂'(N) := O₂'(N) ∩ F(N)`:
the kernel `V ⊓ C_G(K)` is trivial.  The D-group structure lemma puts the
kernel in `O₂(N)` or `E(N)`, and both intersections with `V` are trivial by
hypothesis. -/
private theorem dGroup_faithfulness_bridge
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (N V : Subgroup G)
    (hNtop : N ≠ ⊤) (hV : IsKleinFour V) (hVN : V ≤ N)
    (hV2 : V ⊓ twoCoreOf N = ⊥) (hVE : V ⊓ componentLayerOf N = ⊥) :
    V ⊓ Subgroup.centralizer
      ((oddCoreOf N ⊓ fittingSubgroupOf N : Subgroup G) : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  let K₀ : Subgroup G := V ⊓ Subgroup.centralizer
    ((oddCoreOf N ⊓ fittingSubgroupOf N : Subgroup G) : Set G)
  have hxK₀ : x ∈ K₀ := ⟨hx.1, hx.2⟩
  have hK₀V : K₀ ≤ V := inf_le_left
  have hK₀C : K₀ ≤ Subgroup.centralizer
    ((oddCoreOf N ⊓ fittingSubgroupOf N : Subgroup G) : Set G) := inf_le_right
  rcases dGroup_centralizer_f2p_twoSubgroup_le_twoCore_or_layer
      hmin N V hNtop hV hVN hV2 hVE (K₀ := K₀) hK₀V hK₀C with hK2 | hKE
  · have hxV2 : x ∈ V ⊓ twoCoreOf N := ⟨hx.1, hK2 hxK₀⟩
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [hV2] at hxV2
      exact hxV2
    exact hxbot
  · have hxVE : x ∈ V ⊓ componentLayerOf N := ⟨hx.1, hKE hxK₀⟩
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [hVE] at hxVE
      exact hxVE
    exact hxbot

/-! ## `t ∈ O₂(N_G(X))` centralizes `N_A(X)`, and the 1.1(iv) pair

The paper's final step (`Lying in O₂(N_G(X)), t centralizes N_A(X), hence
(by 1.1.iv) centralizes A`) is split here into its two honest components:

1. `lemma_2_9_t_centralizes_normalizerIn_oddCore`: the 2-core argument.
   If `t ∈ O₂(N_G(X))` and `a ∈ A = O₂'(N) ∩ N_G(X)`, then the commutator
   `[t, a]` lies in `O₂(N_G(X)) ∩ O₂'(N) = 1`, because `O₂(N_G(X))` is a
   `2`-group and `A` has odd order.  This part is proved here.

2. The transfer `centralizes_of_subnormal_selfCentralizing_coprime`
   (`Lemma27Infra`) needs a subnormal self-centralizing subgroup of `K`.
   The re-pinned `K := F₂'(N) = O₂'(N) ∩ F(N)` (paper's `A`, p. 216:
   `F_p(X) = O_p(F(X))`) is normal in `N`, nilpotent, and of odd order;
   the pair is `(K, K₁) = (K, K ∩ N_G(X))`.
   `lemma_2_9_centralizes_oddCore_inf_fitting` is the completed 1.1(iv)
   application for that pair, and the two-involution witness below is
   built with `C_K(t)`, so `X ≤ K` by construction. -/

/-- `O₂'(N)` is normal in `N` (ambient form). -/
private lemma oddCoreOf_isNormalIn {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) : IsNormalIn (oddCoreOf N) N := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, hfx⟩
    rw [← hfx]
    change (f : G) ∈ N
    simp
  · intro h hh k hk
    rcases (Subgroup.mem_map).1 hk with ⟨f, hf, hfk⟩
    rw [← hfk]
    have hconj : (⟨h, hh⟩ : ↥N) * f * (⟨h, hh⟩ : ↥N)⁻¹ ∈ pPrimeCore 2 N :=
      (pPrimeCore_normal (p := 2) (G := N)).conj_mem (n := f) hf (g := ⟨h, hh⟩)
    refine Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : ↥N) * f * (⟨h, hh⟩ : ↥N)⁻¹, hconj, ?_⟩
    rw [hfk]
    simpa using hfk

/-- `F₂'(N) := O₂'(N) ∩ F(N)` is normal in `N`. -/
private lemma oddCore_inf_fitting_isNormalIn {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) : IsNormalIn (oddCoreOf N ⊓ fittingSubgroupOf N) N := by
  have hA : IsNormalIn (oddCoreOf N) N := oddCoreOf_isNormalIn N
  have hF : IsNormalIn (fittingSubgroupOf N) N := fittingSubgroupOf_isNormalIn N
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hA.1 hx.1
  · intro h hh k hk
    exact ⟨hA.2 h hh k hk.1, hF.2 h hh k hk.2⟩

/-- `V ≤ N` implies `V` normalizes `F₂'(N) = O₂'(N) ∩ F(N)` (this
intersection is normal in `N`, and normality is transported to the ambient
subgroup). -/
private lemma subgroup_le_normalizer_oddCore_inf_fitting_of_le
    {G : Type u} [Group G] [Finite G] {N V : Subgroup G} (hVN : V ≤ N) :
    V ≤ Subgroup.normalizer
      ((oddCoreOf N ⊓ fittingSubgroupOf N : Subgroup G) : Set G) := by
  have hK : IsNormalIn (oddCoreOf N ⊓ fittingSubgroupOf N) N :=
    oddCore_inf_fitting_isNormalIn N
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact hK.2 v (hVN hv) a ha
  · intro ha
    have hconj : v⁻¹ * (v * a * v⁻¹) * v ∈ oddCoreOf N ⊓ fittingSubgroupOf N := by
      simpa using (hK.2 v⁻¹ (N.inv_mem (hVN hv)) (v * a * v⁻¹) ha)
    simpa [mul_assoc] using hconj

/-- `F₂'(N) := O₂'(N) ∩ F(N)` is nilpotent (it is a subgroup of the
nilpotent Fitting subgroup). -/
private lemma oddCore_inf_fitting_isNilpotent {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) : Group.IsNilpotent (↥(oddCoreOf N ⊓ fittingSubgroupOf N)) := by
  let F : Subgroup G := fittingSubgroupOf N
  let K : Subgroup G := oddCoreOf N ⊓ F
  have hKF : K ≤ F := inf_le_right
  have : Group.IsNilpotent (↥F) := fittingSubgroupOf_isNilpotent N
  have hsub : Group.IsNilpotent (↥(K.subgroupOf F)) := by infer_instance
  exact Group.nilpotent_of_mulEquiv (G := K.subgroupOf F) (G' := ↥K) (_h := hsub)
    (Subgroup.subgroupOfEquivOfLe hKF)

/-- In a finite nilpotent ambient subgroup `F`, every ambient subgroup
`T ≤ F` is subnormal in `F`. -/
private theorem isSubnormal_of_nilpotent_ambient {G : Type u} [Group G] [Finite G]
    {F : Subgroup G} (hF : Group.IsNilpotent F) (T : Subgroup G) (_hTF : T ≤ F) :
    (T.subgroupOf F).IsSubnormal := by
  classical
  have : Group.IsNilpotent (↥F) := hF
  let P : ℕ → Prop := fun n => ∀ H : Subgroup (↥F), H.index = n → H.IsSubnormal
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih H hn
    by_cases htop : H = ⊤
    · rw [htop]
      exact Subgroup.IsSubnormal.top (G := ↥F)
    · let N := Subgroup.normalizer (H : Set (↥F))
      have hHltN : H < N := Group.normalizerCondition_of_isNilpotent H (lt_top_iff_ne_top.mpr htop)
      have hle : H ≤ N := le_of_lt hHltN
      have hN : (H.subgroupOf N).Normal := by
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer (h := hle)).2 le_rfl
      have hind : N.index < H.index := by
        have hrel : H.relIndex N * N.index = H.index :=
          Subgroup.relIndex_mul_index (h := hle)
        have hrel_ge : 2 ≤ H.relIndex N := by
          have hne_top : H.subgroupOf N ≠ ⊤ := by
            intro htopN
            have hNleH : N ≤ H := (Subgroup.subgroupOf_eq_top (H := H) (K := N)).1 htopN
            exact (ne_of_lt hHltN) (le_antisymm hle hNleH)
          have hone : 1 < H.relIndex N :=
            Subgroup.one_lt_index_of_ne_top (H := H.subgroupOf N) hne_top
          exact hone
        have hindN : 1 ≤ N.index := by
          exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := N)))
        have hb : N.index < 2 * N.index := by omega
        have hb' : 2 * N.index ≤ H.relIndex N * N.index := Nat.mul_le_mul_right N.index hrel_ge
        calc
          N.index < 2 * N.index := hb
          _ ≤ H.relIndex N * N.index := hb'
          _ = H.index := hrel
      have hind' : N.index < n := by
        rw [← hn]
        exact hind
      exact Subgroup.IsSubnormal.step H N hle (ih N.index hind' N rfl) hN
  exact hP (T.subgroupOf F).index (T.subgroupOf F) rfl

/-- `O₂(N_G(X)) ∩ O₂'(N) = ⊥`: a `2`-group meets a `2'`-group trivially. -/
private lemma twoCoreOf_inf_oddCoreOf_eq_bot {G : Type u} [Group G] [Finite G]
    (M N : Subgroup G) : twoCoreOf M ⊓ oddCoreOf N = ⊥ := by
  classical
  have hne2 : Nat.card (↥(twoCoreOf M)) ≠ 0 := (Nat.card_pos (α := (↥(twoCoreOf M)))).ne'
  have hneO : Nat.card (↥(oddCoreOf N)) ≠ 0 := (Nat.card_pos (α := (↥(oddCoreOf N)))).ne'
  have hdisjPF : Disjoint (Nat.card (↥(twoCoreOf M))).primeFactors
      (Nat.card (↥(oddCoreOf N))).primeFactors := by
    refine Finset.disjoint_left.mpr ?_
    intro p hp1 hp2
    have hp1' : p ∈ (Nat.card (↥(piCoreOf M ({2} : Set ℕ)))).primeFactors := by
      simpa [twoCoreOf_eq_piCoreOf_2] using hp1
    have hp2' : p ∈ (Nat.card (↥(piCoreOf N ({q : ℕ | Odd q} : Set ℕ)))).primeFactors := by
      simpa [oddCoreOf_eq_piCoreOf_odd] using hp2
    have hp2p : p = 2 := by
      simpa using (piCoreOf_primeDivisors M ({2} : Set ℕ) p hp1')
    have hpodd : Odd p := piCoreOf_primeDivisors N ({q : ℕ | Odd q} : Set ℕ) p hp2'
    have : ¬ Odd 2 := by norm_num
    exact this (by simpa [hp2p] using hpodd)
  have hcop : Nat.Coprime (Nat.card (↥(twoCoreOf M))) (Nat.card (↥(oddCoreOf N))) :=
    (Nat.disjoint_primeFactors hne2 hneO).mp hdisjPF
  exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)

/-- The 2-core argument: if `t ∈ N` and `t ∈ O₂(N_G(X))`, then `t`
centralizes `N_{O₂'(N)}(X)`.  For `a ∈ O₂'(N) ∩ N_G(X)` the commutator
`[t, a]` lies in `O₂(N_G(X))` (normal 2-subgroup, `a` normalizes `X`) and
in `O₂'(N)` (`t ∈ N`, `O₂'(N) ⊴ N`), hence is trivial. -/
private lemma lemma_2_9_t_centralizes_normalizerIn_oddCore
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) {t : G} (htN : t ∈ N)
    (X : Subgroup G) (htO2 : t ∈ twoCoreOf (Subgroup.normalizer (X : Set G))) :
    Subgroup.zpowers t ≤ Subgroup.centralizer
      ((oddCoreOf N ⊓ Subgroup.normalizer (X : Set G)) : Set G) := by
  classical
  let M : Subgroup G := Subgroup.normalizer (X : Set G)
  let A : Subgroup G := oddCoreOf N
  let O : Subgroup G := twoCoreOf M
  have hAN : IsNormalIn A N := oddCoreOf_isNormalIn N
  have hOM : IsNormalIn O M := by
    have htwo : twoCoreOf M = qCoreOf M 2 := by
      rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton M 2 Nat.prime_two]
    simpa [O, htwo] using (qCoreOf_normal_in M 2)
  have hdisj : O ⊓ A = ⊥ := by simpa [O, A] using (twoCoreOf_inf_oddCoreOf_eq_bot M N)
  intro p hp
  rcases Subgroup.mem_zpowers_iff.mp hp with ⟨n, rfl⟩
  intro a ha
  let c : G := t * a * t⁻¹ * a⁻¹
  have haA : a ∈ A := ha.1
  have haM : a ∈ M := ha.2
  have hcA : c ∈ A := by
    have hta : t * a * t⁻¹ ∈ A := (hAN.2 t htN a haA)
    change (t * a * t⁻¹) * a⁻¹ ∈ A
    exact A.mul_mem hta (A.inv_mem haA)
  have hcO : c ∈ O := by
    have hOinv : t⁻¹ ∈ O := O.inv_mem htO2
    have hat : a * t⁻¹ * a⁻¹ ∈ O := (hOM.2 a haM t⁻¹ hOinv)
    have hceq : c = t * (a * t⁻¹ * a⁻¹) := by
      dsimp [c]
      group
    rw [hceq]
    exact O.mul_mem htO2 hat
  have hcbot : c ∈ (⊥ : Subgroup G) := by
    have hci : c ∈ O ⊓ A := ⟨hcO, hcA⟩
    rw [hdisj] at hci
    exact hci
  have hc1 : c = 1 := by simpa using hcbot
  have htata : t * a * t⁻¹ = a := by
    have hcong := congrArg (fun x : G => x * a) hc1
    have h1 : (t * a * t⁻¹ * a⁻¹) * a = t * a * t⁻¹ := by group
    have h2 : (1 : G) * a = a := by simp
    rw [h1, h2] at hcong
    exact hcong
  have hcomm : Commute t a := by
    have hcong := congrArg (fun x : G => x * t) htata
    have h1 : t * a * t⁻¹ * t = t * a := by group
    rw [h1] at hcong
    exact hcong
  have hcomm' : Commute (t ^ n) a := hcomm.zpow_left n
  exact hcomm'.symm

/-- The completed 1.1(iv) transfer for the paper's pair
`(K, K₁) = (O₂'(N) ∩ F(N), N_K(X))`: `K` is nilpotent (so `K₁` is
subnormal), `K₁` is self-centralizing in `K` (an element of `K`
centralizing `K₁` centralizes `X ≤ K₁`, hence normalizes `X`), and the
orders are coprime with `K` solvable.  The input `htK₁` is
`t` centralizing `K₁`; `lemma_2_9_centralizes_oddCore_inf_fitting_of_mem_twoCore`
supplies it from `t ∈ O₂(N_G(X))` via the 2-core lemma. -/
private theorem lemma_2_9_centralizes_oddCore_inf_fitting
    {G : Type u} [Group G] [Finite G]
    (t : G) (htInv : IsInvolution t) (N X : Subgroup G)
    (hX : X ≤ oddCoreOf N ⊓ fittingSubgroupOf N)
    (htN : t ∈ N)
    (htK₁ : Subgroup.zpowers t ≤ Subgroup.centralizer
      ((oddCoreOf N ⊓ fittingSubgroupOf N ⊓ Subgroup.normalizer (X : Set G)) : Set G)) :
    Subgroup.zpowers t ≤ Subgroup.centralizer (oddCoreOf N ⊓ fittingSubgroupOf N : Set G) := by
  classical
  let K : Subgroup G := oddCoreOf N ⊓ fittingSubgroupOf N
  let K₁ : Subgroup G := K ⊓ Subgroup.normalizer (X : Set G)
  have hK₁leK : K₁ ≤ K := inf_le_left
  have hsub : (K₁.subgroupOf K).IsSubnormal :=
    isSubnormal_of_nilpotent_ambient (oddCore_inf_fitting_isNilpotent N) K₁ hK₁leK
  have hPK : Subgroup.zpowers t ≤ Subgroup.normalizer (K : Set G) := by
    have hK : IsNormalIn K N := by simpa [K] using (oddCore_inf_fitting_isNormalIn N)
    refine Subgroup.zpowers_le.2 ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hK.2 t htN y hy
    · intro hy
      have hconj : t⁻¹ * (t * y * t⁻¹) * t ∈ K := by
        simpa using (hK.2 t⁻¹ (N.inv_mem htN) (t * y * t⁻¹) hy)
      simpa [mul_assoc] using hconj
  have hPK₁ : Subgroup.zpowers t ≤ Subgroup.centralizer (K₁ : Set G) := htK₁
  have hXleK₁ : X ≤ K₁ := le_inf hX (by intro x hx; exact Subgroup.le_normalizer hx)
  have hself : K ⊓ Subgroup.centralizer (K₁ : Set G) ≤ K₁ := by
    intro a ha
    rcases ha with ⟨haK, haC⟩
    refine ⟨haK, ?_⟩
    show a ∈ Subgroup.normalizer (X : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxK₁ : x ∈ K₁ := hXleK₁ hx
      have hacomm : x * a = a * x := (Subgroup.mem_centralizer_iff.mp haC x hxK₁)
      have hax : a * x * a⁻¹ = x := by
        calc
          a * x * a⁻¹ = (x * a) * a⁻¹ := by rw [hacomm]
          _ = x := by group
      rw [hax]
      exact hx
    · intro hx
      have hxK₁ : (a * x * a⁻¹) ∈ K₁ := hXleK₁ hx
      have hacomm : (a * x * a⁻¹) * a = a * (a * x * a⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp haC (a * x * a⁻¹) hxK₁)
      have hxeq : x = a * x * a⁻¹ := by
        calc
          x = a⁻¹ * ((a * x * a⁻¹) * a) := by group
          _ = a⁻¹ * (a * (a * x * a⁻¹)) := by rw [hacomm]
          _ = a * x * a⁻¹ := by group
      rw [hxeq]
      exact hx
  have hcopA : Nat.Coprime 2 (Nat.card (↥(oddCoreOf N))) :=
    Nat.coprime_two_left.mpr (oddCoreOf_odd_card N)
  have hKA : K ≤ oddCoreOf N := inf_le_left
  have hdvd : Nat.card (↥K) ∣ Nat.card (↥(oddCoreOf N)) := by
    have hcard : Nat.card (↥K) = Nat.card (↥(K.subgroupOf (oddCoreOf N))) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv.symm
    rw [hcard]
    exact (K.subgroupOf (oddCoreOf N)).card_subgroup_dvd_card
  have hcopK : Nat.Coprime 2 (Nat.card (↥K)) := Nat.Coprime.of_dvd_right hdvd hcopA
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers t)) (Nat.card (↥K)) := by
    have hcard : Nat.card (Subgroup.zpowers t) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by simpa [pow_two] using htInv.2) htInv.1
    rw [hcard]
    exact hcopK
  have hsolv : IsSolvable (↥K) := odd_order_theorem (G := ↥K) (Nat.coprime_two_left.mp hcopK)
  simpa [K] using
    (centralizes_of_subnormal_selfCentralizing_coprime
      (Subgroup.zpowers t) K K₁ hPK hK₁leK hsub hPK₁ hself hcop hsolv)

/-- The corrected 1.1(iv) application in one step: from
`X ≤ F₂'(N)`, `t ∈ N`, and `t ∈ O₂(N_G(X))`, `t` centralizes
`F₂'(N) := O₂'(N) ∩ F(N)`.  This is the theorem-local replacement for the
final inference of Lemma 2.9 once the two-involution witness is built with
the paper's `A = F₂'(N)` (the current witness only supplies
`X ≤ oddCoreOf N`; see the task card). -/
private theorem lemma_2_9_centralizes_oddCore_inf_fitting_of_mem_twoCore
    {G : Type u} [Group G] [Finite G]
    (t : G) (htInv : IsInvolution t) (N X : Subgroup G)
    (hX : X ≤ oddCoreOf N ⊓ fittingSubgroupOf N)
    (htN : t ∈ N)
    (htO2 : t ∈ twoCoreOf (Subgroup.normalizer (X : Set G))) :
    Subgroup.zpowers t ≤ Subgroup.centralizer (oddCoreOf N ⊓ fittingSubgroupOf N : Set G) := by
  classical
  let K : Subgroup G := oddCoreOf N ⊓ fittingSubgroupOf N
  have htCentNAX : Subgroup.zpowers t ≤ Subgroup.centralizer
      ((oddCoreOf N ⊓ Subgroup.normalizer (X : Set G)) : Set G) :=
    lemma_2_9_t_centralizes_normalizerIn_oddCore N htN X htO2
  have hK₁NAX : (K ⊓ Subgroup.normalizer (X : Set G) : Set G) ⊆
      (oddCoreOf N ⊓ Subgroup.normalizer (X : Set G) : Set G) := by
    intro y hy
    exact ⟨hy.1.1, hy.2⟩
  have hCanti : Subgroup.centralizer ((oddCoreOf N ⊓ Subgroup.normalizer (X : Set G)) : Set G) ≤
      Subgroup.centralizer ((K ⊓ Subgroup.normalizer (X : Set G)) : Set G) :=
    Set.centralizer_subset hK₁NAX
  have htK₁ : Subgroup.zpowers t ≤ Subgroup.centralizer
      ((K ⊓ Subgroup.normalizer (X : Set G)) : Set G) := htCentNAX.trans hCanti
  simpa [K] using (lemma_2_9_centralizes_oddCore_inf_fitting t htInv N X hX htN htK₁)

/-! ## Klein-four fixed-point choice (aligned with `Lemma27Infra`) -/

/-- The aligned "choose `s`" fact: if `V` is a Klein-four subgroup of `N`
acting faithfully on the nontrivial odd core `A = O₂'(N)`, then some
nonidentity `s ∈ V` has nontrivial fixed subgroup in `A`.  This is
`GorensteinWalter.exists_ne_one_fixedPoints_of_kleinFour_action`
instantiated with the conjugation action of `V` on `oddCoreOf N`.  It is an
auxiliary fixed-point theorem; the final proof instead uses the stronger
faithful-pair constructor below, which allows the fixed involution to vary
before conjugating it into the distinguished setup. -/
public theorem lemma_2_9_kleinFour_fixedPoints
    {G : Type u} [Group G] [Finite G]
    {V N : Subgroup G}
    (hV : IsKleinFour V) (hVN : V ≤ N)
    (hAne : oddCoreOf N ≠ ⊥)
    (hfaith : oddCoreOf N ⊓ Subgroup.centralizer (V : Set G) = ⊥) :
    ∃ s : G, s ∈ V ∧ s ≠ 1 ∧
      oddCoreOf N ⊓ Subgroup.centralizer ({s} : Set G) ≠ ⊥ := by
  let A : Subgroup G := oddCoreOf N
  have hVA : V ≤ Subgroup.normalizer (A : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rcases (Subgroup.mem_map).1 ha with ⟨p, hp, rfl⟩
      have hvN : v ∈ N := hVN hv
      have hconj : (⟨v, hvN⟩ : ↥N) * p * (⟨v, hvN⟩ : ↥N)⁻¹ ∈ pPrimeCore 2 N :=
        (pPrimeCore_normal (p := 2) (G := N)).conj_mem p hp (⟨v, hvN⟩ : ↥N)
      exact Subgroup.mem_map.mpr
        ⟨(⟨v, hvN⟩ : ↥N) * p * (⟨v, hvN⟩ : ↥N)⁻¹, hconj, by simp⟩
    · intro ha
      rcases (Subgroup.mem_map).1 ha with ⟨p, hp, hpeq⟩
      have hvN : v ∈ N := hVN hv
      have hconj : (⟨v, hvN⟩ : ↥N)⁻¹ * p * (⟨v, hvN⟩ : ↥N) ∈ pPrimeCore 2 N := by
        simpa using
          ((pPrimeCore_normal (p := 2) (G := N)).conj_mem p hp (⟨v, hvN⟩ : ↥N)⁻¹)
      have hmem : v⁻¹ * (p : G) * v ∈ A :=
        Subgroup.mem_map.mpr
          ⟨(⟨v, hvN⟩ : ↥N)⁻¹ * p * (⟨v, hvN⟩ : ↥N), hconj, by simp⟩
      have heq : a = v⁻¹ * (p : G) * v := by
        calc
          a = v⁻¹ * (v * a * v⁻¹) * v := by group
          _ = v⁻¹ * (p : G) * v := by rw [← hpeq]; rfl
      exact heq ▸ hmem
  have hAodd : Nat.Coprime 2 (Nat.card (↥A)) := by
    dsimp [A, oddCoreOf]
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := N)
  simpa [A] using (exists_ne_one_fixedPoints_of_kleinFour_action
    (G := G) (V := V) (A := A) hV hVA hAodd hAne hfaith)

/-- The local "choose `s`" transfer: if `V` acts fixed-point-freely on the
odd group `A` (`C_A(V) = ⊥`) and `t ∈ V` has `C_A(t) ≠ ⊥`, then some other
nonidentity involution `s ∈ V` does **not** centralize `C_A(t)`, so
`[s, C_A(t)] ≠ ⊥`.  This is the kernel of the paper's two-involution step
(Fact 1.1(iii) + Fact 1.1(i)); it is the precise way
`exists_ne_one_fixedPoints_of_kleinFour_action` is upgraded from
`C_A(s) ≠ ⊥` to the commutator witness. -/
private lemma lemma_2_9_exists_s_commutator_ne_bot
    {G : Type u} [Group G] [Finite G]
    {V A : Subgroup G}
    (hfix : A ⊓ Subgroup.centralizer (V : Set G) = ⊥)
    {t : G}
    (hCt : A ⊓ Subgroup.centralizer ({t} : Set G) ≠ ⊥) :
    ∃ s : G, s ∈ V ∧ s ≠ 1 ∧ s ≠ t ∧
      ¬ (A ⊓ Subgroup.centralizer ({t} : Set G) ≤
        Subgroup.centralizer ({s} : Set G)) := by
  classical
  let C : Subgroup G := A ⊓ Subgroup.centralizer ({t} : Set G)
  by_contra hnone
  push Not at hnone
  have hAll : ∀ v : G, v ∈ V → v ≠ 1 → v ≠ t →
      C ≤ Subgroup.centralizer ({v} : Set G) := by
    intro v hv hv1 hvt
    exact hnone v hv hv1 hvt
  have hCfix : C ≤ Subgroup.centralizer (V : Set G) := by
    intro c hc v hv
    by_cases hv1 : v = 1
    · subst v
      simp
    · by_cases hvt : v = t
      · subst v
        have hcC : c ∈ C := hc
        have hcomm : t * c = c * t :=
          (Subgroup.mem_centralizer_iff.mp hcC.2 t (by simp))
        exact hcomm
      · exact (Subgroup.mem_centralizer_iff.mp
          (hAll v hv hv1 hvt hc) v (by simp))
  have hCinf : C ≤ A ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf (by intro c hc; exact hc.1) hCfix
  have hCbot : C = ⊥ := by
    apply le_bot_iff.mp
    intro c hc
    have hcb : c ∈ A ⊓ Subgroup.centralizer (V : Set G) := hCinf hc
    have hbot : c ∈ (⊥ : Subgroup G) := by
      rw [hfix] at hcb
      exact hcb
    exact hbot
  exact hCt (by simpa [C] using hCbot)

/-- Bender 1.1(i), ambient subgroup form: if `P` normalizes `K`, `P` is
coprime to `K`, and `K` is solvable, then the second commutator subgroup
`⁅⁅K, P⁆, P⁆` equals the first `⁅K, P⁆`.  This is the theorem-local wrapper
for `commutatorAction₂_eq_commutatorAction_of_coprime` (and its solvable
Hall variant), used to discharge the `⁅⟨s⟩, X⁆ = X` side condition of
`Lemma29Hypothesis`. -/
private theorem commutator_double_eq_self_of_coprime_solvable
    {G : Type u} [Group G] [Finite G]
    (P K : Subgroup G) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card (↥K)))
    (hsolv : IsSolvable K) :
    ⁅⁅K, P⁆, P⁆ = ⁅K, P⁆ := by
  classical
  let : Subgroup.Normalizes P K := ⟨hPK⟩
  let : MulDistribMulAction (↥P) (↥K) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer P K hPK
  let C : Subgroup (↥K) := commutatorAction (A := ↥P) (G := ↥K)
  have hCmap : C.map K.subtype = ⁅K, P⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator K P hPK
  have hC2eq : commutatorAction₂ (A := ↥P) (G := ↥K) = C :=
    commutatorAction₂_eq_commutatorAction_of_solvable_coprime
      (G := ↥K) (A := ↥P) hsolv hcop
  have hXle : ⁅⁅K, P⁆, P⁆ ≤ ⁅K, P⁆ := by
    exact (Subgroup.le_normalizer_iff_commutator_le_left).mp
      (Subgroup.normalizer_commutator_ge_right K P)
  have hcomm₂_le :
      (commutatorAction₂ (A := ↥P) (G := ↥K)).map K.subtype ≤
        ⁅⁅K, P⁆, P⁆ := by
    let S : Set (↥K) := {x : ↥K | ∃ a : ↥P, ∃ k : ↥K,
      k ∈ C ∧ x = k⁻¹ * (a • k)}
    calc
      (commutatorAction₂ (A := ↥P) (G := ↥K)).map K.subtype =
          (Subgroup.closure S).map K.subtype := by
            rfl
      _ = Subgroup.closure (K.subtype '' S) := by
            simpa using (MonoidHom.map_closure (f := K.subtype) S)
      _ ≤ ⁅⁅K, P⁆, P⁆ := by
            refine (Subgroup.closure_le (K := ⁅⁅K, P⁆, P⁆)).2 ?_
            rintro _ ⟨y, hy, rfl⟩
            rcases hy with ⟨a, k, hkC, rfl⟩
            have hkX : (k : G) ∈ ⁅K, P⁆ := by
              rw [← hCmap]
              exact Subgroup.mem_map.mpr ⟨k, hkC, rfl⟩
            have hgen : ⁅((k : ↥K) : G)⁻¹, (a : G)⁆ ∈ ⁅⁅K, P⁆, P⁆ :=
              Subgroup.commutator_mem_commutator (H₁ := ⁅K, P⁆) (H₂ := P)
                (Subgroup.inv_mem (H := ⁅K, P⁆) hkX) a.2
            simpa [commutatorElement_def,
              Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
              mul_assoc] using hgen
  apply le_antisymm hXle
  intro x hx
  have hx₂ : x ∈ (commutatorAction₂ (A := ↥P) (G := ↥K)).map K.subtype := by
    rw [hC2eq, hCmap]
    exact hx
  exact hcomm₂_le hx₂

/-- If both factors of a commutator subgroup centralize `T`, then the
commutator subgroup itself centralizes `T` (Three Subgroups Lemma).  This is
the theorem-local glue used to prove that the distinguished involution `t`
centralizes `X = [⟨s⟩, C_A(t)]`. -/
private lemma commutator_centralizes_of_centralizing
    {G : Type u} [Group G]
    (P C T : Subgroup G)
    (hPT : P ≤ Subgroup.centralizer (T : Set G))
    (hCT : C ≤ Subgroup.centralizer (T : Set G)) :
    T ≤ Subgroup.centralizer ((⁅P, C⁆ : Subgroup G) : Set G) := by
  have hPTbot : ⁅P, T⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hPT
  have hCTbot : ⁅C, T⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hCT
  have h1 : ⁅⁅C, T⁆, P⁆ = ⊥ := by simp [hCTbot]
  have h2 : ⁅⁅T, P⁆, C⁆ = ⊥ := by
    rw [Subgroup.commutator_comm T P]
    simp [hPTbot]
  have hXT : ⁅⁅P, C⁆, T⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate
      (H₁ := P) (H₂ := C) (H₃ := T) h1 h2
  have hTX : ⁅T, ⁅P, C⁆⁆ = ⊥ := by
    simpa [Subgroup.commutator_comm] using hXT
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hTX

/-- The centralizer of a single element is contained in the centralizer of
the cyclic subgroup it generates. -/
private lemma centralizer_singleton_le_centralizer_zpowers
    {G : Type u} [Group G] (t : G) :
    Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  intro x hx y hy
  rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
  have htx : t * x = x * t :=
    (Subgroup.mem_centralizer_iff.mp hx t (by simp))
  have hxt : Commute x t := htx.symm
  exact (hxt.zpow_right n).symm

/-- In a Klein four subgroup, any two elements commute, hence their cyclic
subgroups centralize each other. -/
private lemma zpowers_le_centralizer_zpowers_of_mem_kleinFour
    {G : Type u} [Group G]
    {V : Subgroup G} (hV : IsKleinFour V) {s t : G}
    (hsV : s ∈ V) (htV : t ∈ V) :
    Subgroup.zpowers s ≤
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  intro x hx y hy
  rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
  rcases Subgroup.mem_zpowers_iff.mp hy with ⟨m, rfl⟩
  let sV : ↥V := ⟨s, hsV⟩
  let tV : ↥V := ⟨t, htV⟩
  have hst : s * t = t * s :=
    congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := V)).is_comm.comm sV tV)
  have hcomm : Commute s t := hst
  exact (hcomm.zpow_zpow n m).symm

/-- In a Klein four subgroup, an element `s` normalizes `C_A(t)` whenever it
normalizes `A` (it also commutes with `t`).  This is the normalization side
condition needed for the 1.1(i) identity on `[⟨s⟩, C_A(t)]`. -/
private lemma centralizerIn_normalizer_of_mem_kleinFour
    {G : Type u} [Group G]
    {V : Subgroup G} (hV : IsKleinFour V)
    {A : Subgroup G} {s t : G}
    (hsV : s ∈ V) (htV : t ∈ V)
    (hPnormA : Subgroup.zpowers s ≤ Subgroup.normalizer (A : Set G)) :
    Subgroup.zpowers s ≤ Subgroup.normalizer (centralizerIn A t : Set G) := by
  classical
  let P : Subgroup G := Subgroup.zpowers s
  let C : Subgroup G := centralizerIn A t
  let T : Subgroup G := Subgroup.zpowers t
  have hPT : P ≤ Subgroup.centralizer (T : Set G) := by
    simpa [P, T] using (zpowers_le_centralizer_zpowers_of_mem_kleinFour hV hsV htV)
  have hCT : C ≤ Subgroup.centralizer (T : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    have hct : t * c = c * t :=
      (Subgroup.mem_centralizer_iff.mp hc.2 t (by simp))
    have hcT : Commute c t := hct.symm
    exact (hcT.zpow_right n).symm
  have hCPA : ⁅C, P⁆ ≤ A := by
    have hPA : ⁅A, P⁆ ≤ A :=
      (Subgroup.le_normalizer_iff_commutator_le_left (H := P) (K := A)).1 hPnormA
    have hCP_le_AP : ⁅C, P⁆ ≤ ⁅A, P⁆ :=
      Subgroup.commutator_mono (H₁ := C) (K₁ := A)
        (by intro c hc; exact hc.1) (K₂ := P) (H₂ := P) le_rfl
    exact hCP_le_AP.trans hPA
  have hCPT : ⁅C, P⁆ ≤ Subgroup.centralizer ({t} : Set G) := by
    have hcomm : T ≤ Subgroup.centralizer ((⁅P, C⁆ : Subgroup G) : Set G) :=
      commutator_centralizes_of_centralizing P C T hPT hCT
    have hXT : ⁅T, ⁅P, C⁆⁆ = ⊥ :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hcomm
    have hX : ⁅⁅P, C⁆, T⁆ = ⊥ := by
      simpa [Subgroup.commutator_comm] using hXT
    have hXleT : ⁅P, C⁆ ≤ Subgroup.centralizer (T : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hX
    have hXC : ⁅C, P⁆ ≤ Subgroup.centralizer (T : Set G) := by
      simpa [Subgroup.commutator_comm] using hXleT
    intro x hx
    have hxT : x ∈ Subgroup.centralizer (T : Set G) := hXC hx
    exact (Subgroup.centralizer_le (show ({t} : Set G) ⊆ (T : Set G) from by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact Subgroup.mem_zpowers t)) hxT
  have hCPC : ⁅C, P⁆ ≤ C := le_inf hCPA hCPT
  exact (Subgroup.le_normalizer_iff_commutator_le_left (H := P) (K := C)).mpr hCPC

/-- `V ≤ N` implies `V` normalizes `O₂'(N)` (the odd core is normal in
`N`, and normality is transported to the ambient subgroup). -/
private lemma subgroup_le_normalizer_oddCoreOf_of_le
    {G : Type u} [Group G] {N V : Subgroup G} (hVN : V ≤ N) :
    V ≤ Subgroup.normalizer (oddCoreOf N : Set G) := by
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rcases (Subgroup.mem_map).1 ha with ⟨p, hp, rfl⟩
    have hvN : v ∈ N := hVN hv
    have hconj : (⟨v, hvN⟩ : ↥N) * p * (⟨v, hvN⟩ : ↥N)⁻¹ ∈ pPrimeCore 2 N :=
      (pPrimeCore_normal (p := 2) (G := N)).conj_mem p hp (⟨v, hvN⟩ : ↥N)
    exact Subgroup.mem_map.mpr
      ⟨(⟨v, hvN⟩ : ↥N) * p * (⟨v, hvN⟩ : ↥N)⁻¹, hconj, by simp⟩
  · intro ha
    rcases (Subgroup.mem_map).1 ha with ⟨p, hp, hpeq⟩
    have hvN : v ∈ N := hVN hv
    have hconj : (⟨v, hvN⟩ : ↥N)⁻¹ * p * (⟨v, hvN⟩ : ↥N) ∈ pPrimeCore 2 N := by
      simpa using
        ((pPrimeCore_normal (p := 2) (G := N)).conj_mem p hp (⟨v, hvN⟩ : ↥N)⁻¹)
    have hmem : v⁻¹ * (p : G) * v ∈ oddCoreOf N :=
      Subgroup.mem_map.mpr
        ⟨(⟨v, hvN⟩ : ↥N)⁻¹ * p * (⟨v, hvN⟩ : ↥N), hconj, by simp⟩
    have heq : a = v⁻¹ * (p : G) * v := by
      calc
        a = v⁻¹ * (v * a * v⁻¹) * v := by group
        _ = v⁻¹ * (p : G) * v := by rw [← hpeq]; rfl
    exact heq ▸ hmem

/-- A faithful Klein-four action on an odd group supplies the pair actually
needed by the paper: for every fixed nonidentity `s ∈ V`, some other
nonidentity `v ∈ V` has `s` acting nontrivially on `C_A(v)`.  The proof uses
the coprime-action generation theorem
`A = ⟨C_A(v) | v ∈ V#⟩`: if `s` centralized every such fixed subgroup, it
would centralize all of `A`, contradicting the faithful kernel.  Unlike the
discarded fixed-`c.t` bridge, this statement is valid in the audited
`C₃ⁿ ⋊ D₈` models. -/
private theorem exists_faithful_action_pair
    {G : Type u} [Group G] [Finite G]
    {V A : Subgroup G}
    (hV : IsKleinFour V)
    (hVA : V ≤ Subgroup.normalizer (A : Set G))
    (hAodd : Nat.Coprime 2 (Nat.card (↥A)))
    (hfaith : V ⊓ Subgroup.centralizer (A : Set G) = ⊥)
    {s : G} (hsV : s ∈ V) (hs1 : s ≠ 1) :
    ∃ v : G, v ∈ V ∧ v ≠ 1 ∧ v ≠ s ∧
      ¬ (centralizerIn A v ≤ Subgroup.centralizer ({s} : Set G)) := by
  classical
  let : IsKleinFour (↥V) := hV
  let : IsMulCommutative (↥V) := IsKleinFour.isMulCommutative
  let : CommGroup (↥V) := IsMulCommutative.instCommGroup
  have hV2 : IsPGroup 2 (↥V) := IsPGroup.of_card (n := 2) (by
    simpa [IsKleinFour.card_four])
  let : Fact (IsPGroup 2 (↥V)) := ⟨hV2⟩
  let : V.Normalizes A := ⟨hVA⟩
  let : MulDistribMulAction (↥V) (↥A) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer V A hVA
  by_contra hnone
  push Not at hnone
  have hfixed_map_le :
      ∀ v : ↥V, ∀ hv1 : v ≠ 1,
        (fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥A)).map A.subtype ≤
          Subgroup.centralizer ({s} : Set G) := by
    intro v hv1
    have hfix_eq :
        fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥A) =
          (elementCentralizerIn A (v : G)).subgroupOf A := by
      simpa using
        fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn A V hVA v
    have hfix_map :
        (fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥A)).map A.subtype =
          centralizerIn A (v : G) := by
      calc
        (fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥A)).map A.subtype =
            ((elementCentralizerIn A (v : G)).subgroupOf A).map A.subtype := by
              rw [hfix_eq]
        _ = elementCentralizerIn A (v : G) ⊓ A := by
              rw [Subgroup.subgroupOf_map_subtype]
        _ = elementCentralizerIn A (v : G) := inf_eq_left.2 inf_le_left
        _ = centralizerIn A (v : G) := rfl
    rw [hfix_map]
    by_cases hvs : (v : G) = s
    · subst hvs
      exact inf_le_right
    · exact hnone (v : G) v.2 (by
        intro hvG
        exact hv1 (Subtype.ext hvG)) hvs
  have htop :=
    iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
      (G := ↥A) (A := ↥V) (p := 2) (hG := hAodd)
      (hncyc := IsKleinFour.not_isCyclic)
  have hAleCent : A ≤ Subgroup.centralizer ({s} : Set G) := by
    have htop_map : (⊤ : Subgroup (↥A)).map A.subtype = A := by
      simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := A))
    calc
      A = (⊤ : Subgroup (↥A)).map A.subtype := htop_map.symm
      _ = (⨆ (v : ↥V) (_ : v ≠ 1),
          fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥A)).map A.subtype := by
            simp [htop]
      _ ≤ Subgroup.centralizer ({s} : Set G) := by
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro v
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro hv1
        exact hfixed_map_le v hv1
  have hsCentA : s ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hAleCent ha) s (by simp)).symm
  have hsKer : s ∈ V ⊓ Subgroup.centralizer (A : Set G) := ⟨hsV, hsCentA⟩
  have hsBot : s ∈ (⊥ : Subgroup G) := by
    rw [hfaith] at hsKer
    exact hsKer
  exact hs1 (by simpa using hsBot)

/-- Inner automorphisms transport the ambient two-core of a subgroup
normalizer.  This is the exact transport needed after applying the local
Lemma 2.9 hypothesis to a conjugate of the faithful-action pair. -/
private lemma map_twoCoreOf_normalizer_eq
    {G : Type u} [Group G] [Finite G]
    (X : Subgroup G) (e : G ≃* G) :
    (twoCoreOf (Subgroup.normalizer (X : Set G))).map e.toMonoidHom =
      twoCoreOf (Subgroup.normalizer (X.map e.toMonoidHom : Set G)) := by
  let M : Subgroup G := Subgroup.normalizer (X : Set G)
  let M' : Subgroup G := Subgroup.normalizer (X.map e.toMonoidHom : Set G)
  have hM : M.map e.toMonoidHom = M' := by
    simpa [M, M'] using Subgroup.map_equiv_normalizer_eq X e
  let eMap : M ≃* M.map e.toMonoidHom :=
    Subgroup.equivMapOfInjective M e.toMonoidHom e.injective
  let eM : M ≃* M' := eMap.trans (MulEquiv.subgroupCongr hM)
  have hcore : (pCore 2 M).map eM.toMonoidHom = pCore 2 M' :=
    pCore_map_iso 2 eM
  have hcomp : M'.subtype.comp eM.toMonoidHom = e.toMonoidHom.comp M.subtype := by
    ext x
    rfl
  unfold twoCoreOf
  have h := congrArg (Subgroup.map M'.subtype) hcore
  rw [Subgroup.map_map, hcomp] at h
  simpa [M, M', Subgroup.map_map] using h

/-- A Klein-four subgroup remains Klein four under an ambient group
automorphism. -/
private lemma isKleinFour_map_mulEquiv
    {G : Type u} [Group G] [Finite G]
    (V : Subgroup G) (hV : IsKleinFour V) (e : G ≃* G) :
    IsKleinFour (V.map e.toMonoidHom) := by
  let eV : V ≃* V.map e.toMonoidHom :=
    Subgroup.equivMapOfInjective V e.toMonoidHom e.injective
  exact {
    card_four := (Nat.card_congr eV.toEquiv).symm.trans hV.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eV.symm).trans hV.exponent_two
  }

/-- Transport a faithful-action pair to the fixed Section-2 setup.  First
conjugate its second involution `v` to `c.t`; then, inside
`H = C_G(c.t)`, conjugate a Sylow subgroup containing the image of `V` to
the fixed Sylow `c.S`.  The image of `X` is an odd subgroup of `H`, hence is
contained in `U`, so `Lemma29Hypothesis` applies.  Finally transport the
resulting two-core membership back to the original `v`. -/
private theorem transport_local_to_pair
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hlocal : Lemma29Hypothesis c)
    {V X : Subgroup G} {s v : G}
    (hV : IsKleinFour V)
    (hsV : s ∈ V) (hvV : v ∈ V) (hv1 : v ≠ 1)
    (hXne : X ≠ ⊥)
    (hXodd : Nat.Coprime 2 (Nat.card (↥X)))
    (hXcomm : ⁅Subgroup.zpowers s, X⁆ = X)
    (hvX : Subgroup.zpowers v ≤ Subgroup.centralizer (X : Set G)) :
    v ∈ twoCoreOf (Subgroup.normalizer (X : Set G)) := by
  classical
  have hv2 : v ^ 2 = 1 := by
    simpa [pow_two] using
      (congrArg Subtype.val (IsKleinFour.mul_self (⟨v, hvV⟩ : ↥V)))
  obtain ⟨g, hgv⟩ :=
    fact_2_preamble_involutions_conjugate_proved hmin v c.t
      ⟨hv1, hv2⟩ c.t_involution
  let eg : G ≃* G := MulAut.conj g
  let Vg : Subgroup G := V.map eg.toMonoidHom
  have hVg : IsKleinFour Vg := isKleinFour_map_mulEquiv V hV eg
  have htVg : c.t ∈ Vg := by
    exact Subgroup.mem_map.mpr ⟨v, hvV, by
      simpa [eg, MulAut.conj_apply] using hgv⟩
  have hVgH : Vg ≤ c.H := by
    intro x hx
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_iff]
    intro z hz
    have hzt : z = c.t := by simpa using hz
    rw [hzt]
    let tVg : ↥Vg := ⟨c.t, htVg⟩
    let xVg : ↥Vg := ⟨x, hx⟩
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := Vg)).is_comm.comm tVg xVg)
  let VgH : Subgroup c.H := Vg.subgroupOf c.H
  have hVgHp : IsPGroup 2 VgH := by
    have hVgp : IsPGroup 2 Vg :=
      IsPGroup.of_card (n := 2) (by simpa [hVg.card_four])
    exact hVgp.of_equiv (Subgroup.subgroupOfEquivOfLe hVgH).symm
  obtain ⟨Q, hVgHQ⟩ := IsPGroup.exists_le_sylow (G := c.H) hVgHp
  have hSH : (c.S : Subgroup G) ≤ c.H := centralizerSetup_S_le_H c
  let P : Sylow 2 c.H := by
    refine {
      toSubgroup := (c.S : Subgroup G).subgroupOf c.H
      isPGroup' := c.S.isPGroup'.of_equiv
        (Subgroup.subgroupOfEquivOfLe hSH).symm
      is_maximal' := ?_
    }
    intro Q hQ hPQ
    have hQmap : IsPGroup 2 (Q.map c.H.subtype) := hQ.map c.H.subtype
    have hPmap : (c.S : Subgroup G) ≤ Q.map c.H.subtype := by
      intro x hx
      have hxH : x ∈ c.H := hSH hx
      have hxPQ : (⟨x, hxH⟩ : c.H) ∈
          (c.S : Subgroup G).subgroupOf c.H := hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, hPQ hxPQ, rfl⟩
    have hmap : Q.map c.H.subtype = (c.S : Subgroup G) :=
      c.S.is_maximal' hQmap hPmap
    apply (Subgroup.map_subtype_inj).mp
    rw [hmap, Subgroup.map_subgroupOf_eq_of_le hSH]
  obtain ⟨h, hh⟩ :=
    @MulAction.IsPretransitive.exists_smul_eq c.H (Sylow 2 c.H)
      inferInstance inferInstance Q P
  let q : G := (h : G) * g
  let eq : G ≃* G := MulAut.conj q
  have hqv : eq v = c.t := by
    have hht : (h : G) * c.t * (h : G)⁻¹ = c.t := by
      have hhcent : (h : G) ∈ Subgroup.centralizer ({c.t} : Set G) := by
        rw [← c.H_eq_centralizer]
        exact h.2
      rw [Subgroup.mem_centralizer_iff] at hhcent
      have hcomm : c.t * (h : G) = (h : G) * c.t :=
        hhcent c.t (by simp)
      calc
        (h : G) * c.t * (h : G)⁻¹ = (c.t * (h : G)) * (h : G)⁻¹ := by rw [hcomm]
        _ = c.t := by group
    change q * v * q⁻¹ = c.t
    rw [show q = (h : G) * g by rfl]
    calc
      ((h : G) * g) * v * ((h : G) * g)⁻¹ =
          (h : G) * (g * v * g⁻¹) * (h : G)⁻¹ := by group
      _ = (h : G) * c.t * (h : G)⁻¹ := by rw [hgv]
      _ = c.t := hht
  have hmapV_le_S : V.map eq.toMonoidHom ≤ (c.S : Subgroup G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyV, hxy⟩
    let yg : G := eg y
    have hygVg : yg ∈ Vg := Subgroup.mem_map.mpr ⟨y, hyV, rfl⟩
    have hygH : yg ∈ c.H := hVgH hygVg
    let ygH : c.H := ⟨yg, hygH⟩
    have hygVgH : ygH ∈ VgH := hygVg
    have hygQ : ygH ∈ (Q : Subgroup c.H) := hVgHQ hygVgH
    have hconjQ : (h : c.H) * ygH * (h : c.H)⁻¹ ∈
        ((h : c.H) • Q : Sylow 2 c.H) := by
      change (MulAut.conj (h : c.H)) ygH ∈
        (Q : Subgroup c.H).map (MulAut.conj (h : c.H)).toMonoidHom
      exact Subgroup.mem_map.mpr ⟨ygH, hygQ, rfl⟩
    rw [hh] at hconjQ
    have hconjSsub : (h : c.H) * ygH * (h : c.H)⁻¹ ∈
        (c.S : Subgroup G).subgroupOf c.H := by
      change (h : c.H) * ygH * (h : c.H)⁻¹ ∈ (P : Subgroup c.H) at hconjQ
      simpa [P] using hconjQ
    have hxy' : x = (h : G) * yg * (h : G)⁻¹ := by
      calc
        x = eq y := hxy.symm
        _ = (h : G) * yg * (h : G)⁻¹ := by
          simp only [eq, q, yg, eg, MulAut.conj_apply]
          group
    rw [hxy']
    exact hconjSsub
  let s' : G := eq s
  let X' : Subgroup G := X.map eq.toMonoidHom
  have hs'S : s' ∈ (c.S : Subgroup G) :=
    hmapV_le_S (Subgroup.mem_map.mpr ⟨s, hsV, rfl⟩)
  have hX'ne : X' ≠ ⊥ := by
    intro hbot
    apply hXne
    exact (Subgroup.map_eq_bot_iff_of_injective X eq.injective).mp hbot
  have hX'odd : Nat.Coprime 2 (Nat.card (↥X')) := by
    have eX : X ≃* X' := Subgroup.equivMapOfInjective X eq.toMonoidHom eq.injective
    rw [← Nat.card_congr eX.toEquiv]
    exact hXodd
  have htX' : Subgroup.zpowers c.t ≤ Subgroup.centralizer (X' : Set G) := by
    intro z hz x hx
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨y, hyX, rfl⟩
    have hvCent : v ∈ Subgroup.centralizer (X : Set G) :=
      hvX (Subgroup.mem_zpowers v)
    have hvy : y * v = v * y :=
      Subgroup.mem_centralizer_iff.mp hvCent y hyX
    have hvyComm : Commute v y := hvy.symm
    have hvn : Commute (v ^ n) y := hvyComm.zpow_left n
    have hmapComm : Commute (eq (v ^ n)) (eq y) := hvn.map eq.toMonoidHom
    simpa [map_zpow, hqv] using hmapComm.eq.symm
  have hX'H : X' ≤ c.H := by
    intro x hx
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_iff]
    intro z hz
    have hzt : z = c.t := by simpa using hz
    rw [hzt]
    exact (Subgroup.mem_centralizer_iff.mp
      (htX' (Subgroup.mem_zpowers c.t)) x hx).symm
  have hX'U : X' ≤ c.U :=
    odd_order_subgroup_le_U_of_H_eq_SU hmin c hX'H hX'odd
  have hX'comm : ⁅Subgroup.zpowers s', X'⁆ = X' := by
    have hmap := congrArg (Subgroup.map eq.toMonoidHom) hXcomm
    simpa [s', X', Subgroup.map_commutator, MonoidHom.map_zpowers] using hmap
  have htO2' := hlocal s' X' hs'S hX'ne hX'U hX'comm
  have hcoreMap := map_twoCoreOf_normalizer_eq X eq
  have htMap : c.t ∈
      (twoCoreOf (Subgroup.normalizer (X : Set G))).map eq.toMonoidHom := by
    rw [hcoreMap]
    exact htO2'
  rcases Subgroup.mem_map.mp htMap with ⟨w, hw, hew⟩
  have hwv : w = v := eq.injective (hew.trans hqv.symm)
  simpa [hwv] using hw

/-- A faithful Klein-four action supplies the commutator pair needed for
the transport argument.  Fix the distinguished involution `c.t`; choose a
different nonidentity `v ∈ V` on whose fixed subgroup `c.t` acts
nontrivially, and put `X = [⟨c.t⟩, C_A(v)]` for
`A = O₂'(N) ∩ F(N)`.  Then `X` is nontrivial and odd, is stable under the
`c.t`-commutator action, and is centralized by `v`. -/
private theorem lemma_2_9_two_involution_bridge
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    {V N : Subgroup G}
    (hVN : V ≤ N) (htV : c.t ∈ V) (hV : IsKleinFour V)
    (hfaith : V ⊓ Subgroup.centralizer
      ((oddCoreOf N ⊓ fittingSubgroupOf N : Subgroup G) : Set G) = ⊥) :
    ∃ v : G, ∃ X : Subgroup G,
      v ∈ V ∧ v ≠ 1 ∧ v ≠ c.t ∧ X ≠ ⊥ ∧
        X ≤ oddCoreOf N ⊓ fittingSubgroupOf N ∧
        Nat.Coprime 2 (Nat.card (↥X)) ∧
        ⁅Subgroup.zpowers c.t, X⁆ = X ∧
          Subgroup.zpowers v ≤ Subgroup.centralizer (X : Set G) := by
  classical
  let A : Subgroup G := oddCoreOf N ⊓ fittingSubgroupOf N
  have hVA : V ≤ Subgroup.normalizer (A : Set G) :=
    subgroup_le_normalizer_oddCore_inf_fitting_of_le hVN
  have hAodd : Nat.Coprime 2 (Nat.card (↥A)) := by
    dsimp [A]
    have hcopA : Nat.Coprime 2 (Nat.card (↥(oddCoreOf N))) :=
      Nat.coprime_two_left.mpr (oddCoreOf_odd_card N)
    have hdvd : Nat.card (↥(oddCoreOf N ⊓ fittingSubgroupOf N)) ∣
        Nat.card (↥(oddCoreOf N)) := by
      have hKA : (oddCoreOf N ⊓ fittingSubgroupOf N) ≤ oddCoreOf N := inf_le_left
      have hcard : Nat.card (↥(oddCoreOf N ⊓ fittingSubgroupOf N)) =
          Nat.card (↥((oddCoreOf N ⊓ fittingSubgroupOf N).subgroupOf (oddCoreOf N))) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv.symm
      rw [hcard]
      exact ((oddCoreOf N ⊓ fittingSubgroupOf N).subgroupOf (oddCoreOf N)).card_subgroup_dvd_card
    exact Nat.Coprime.of_dvd_right hdvd hcopA
  rcases exists_faithful_action_pair hV hVA hAodd hfaith
      htV c.t_involution.1 with
    ⟨v, hvV, hv1, hvt, hnotCent⟩
  let P : Subgroup G := Subgroup.zpowers c.t
  let C : Subgroup G := centralizerIn A v
  let X : Subgroup G := ⁅P, C⁆
  have hCA : C ≤ A := by intro c hc; exact hc.1
  have hPC : P ≤ Subgroup.normalizer (C : Set G) :=
    centralizerIn_normalizer_of_mem_kleinFour hV htV hvV
      (by simpa [P] using (Subgroup.zpowers_le.2 (hVA htV)))
  have hCcard : Nat.card (↥C) ∣ Nat.card (↥A) := by
    have h := (C.subgroupOf A).card_subgroup_dvd_card
    have h' : Nat.card (↥(C.subgroupOf A)) = Nat.card (↥C) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv
    simpa [h'] using h
  have hCodd : Nat.Coprime 2 (Nat.card (↥C)) :=
    Nat.Coprime.of_dvd_right hCcard hAodd
  have htOrd : orderOf c.t = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using c.t_involution.2)
      c.t_involution.1
  have hCsolv : IsSolvable C :=
    odd_order_theorem (G := ↥C)
      (Nat.coprime_two_left.mp hCodd)
  have hXcomm' : ⁅⁅C, P⁆, P⁆ = ⁅C, P⁆ :=
    commutator_double_eq_self_of_coprime_solvable P C hPC
      (by simpa [P, htOrd] using hCodd) hCsolv
  have hXcomm : ⁅P, X⁆ = X := by
    simpa [X, Subgroup.commutator_comm] using hXcomm'
  have hXA : X ≤ A := by
    have hPA : P ≤ Subgroup.normalizer (A : Set G) :=
      Subgroup.zpowers_le.2 (hVA htV)
    have hAP : ⁅A, P⁆ ≤ A :=
      (Subgroup.le_normalizer_iff_commutator_le_left (H := P) (K := A)).1 hPA
    have hle : ⁅P, C⁆ ≤ ⁅A, P⁆ := by
      simpa [Subgroup.commutator_comm] using
        (Subgroup.commutator_mono (H₁ := P) (K₁ := P) le_rfl
          (H₂ := C) (K₂ := A) hCA)
    simpa [X] using hle.trans hAP
  let T : Subgroup G := Subgroup.zpowers v
  have hPT : P ≤ Subgroup.centralizer (T : Set G) := by
    simpa [P, T] using
      (zpowers_le_centralizer_zpowers_of_mem_kleinFour hV htV hvV)
  have hCT : C ≤ Subgroup.centralizer (T : Set G) := by
    intro c0 hc0
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    have hct : v * c0 = c0 * v :=
      (Subgroup.mem_centralizer_iff.mp hc0.2 v (by simp))
    have hcT : Commute c0 v := hct.symm
    exact (hcT.zpow_right n).symm
  have hvX : Subgroup.zpowers v ≤ Subgroup.centralizer (X : Set G) := by
    have h := commutator_centralizes_of_centralizing P C T hPT hCT
    simpa [X, T] using h
  have hXne : X ≠ ⊥ := by
    intro hXbot
    apply hnotCent
    change C ≤ Subgroup.centralizer ({c.t} : Set G)
    intro c0 hc0
    have hPleC : P ≤ Subgroup.centralizer (C : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hXbot
    have hsC : c.t ∈ Subgroup.centralizer (C : Set G) :=
      hPleC (Subgroup.mem_zpowers c.t)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hys : y = c.t := by simpa using hy
    rw [hys]
    exact ((Subgroup.mem_centralizer_iff.mp hsC c0 hc0)).symm
  have hXcard : Nat.card (↥X) ∣ Nat.card (↥A) := by
    have h := (X.subgroupOf A).card_subgroup_dvd_card
    have h' : Nat.card (↥(X.subgroupOf A)) = Nat.card (↥X) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXA).toEquiv
    simpa [h'] using h
  have hXodd : Nat.Coprime 2 (Nat.card (↥X)) :=
    Nat.Coprime.of_dvd_right hXcard hAodd
  refine ⟨v, X, hvV, hv1, hvt, hXne, hXA, hXodd, hXcomm, hvX⟩

/-- **REGISTERED GLUE BRIDGE**, re-pinned 2026-08-16 and now **PROVED**:
from the `Lemma29Hypothesis` conclusion `t ∈ O₂(N_G(X))` and the
two-involution witness (`X ≤ K = F₂'(N) := O₂'(N) ∩ F(N)`), `t`
centralizes `K`.  Proof: `lemma_2_9_t_centralizes_normalizerIn_oddCore`
(2-core argument) gives `t` centralizing `N_K(X)`, and the completed
1.1(iv) transfer
`lemma_2_9_centralizes_oddCore_inf_fitting_of_mem_twoCore` applies to the
pair `(K, K ∩ N_G(X))` (`K` nilpotent ⇒ subnormal, self-centralizing,
coprime, solvable). -/
private theorem lemma_2_9_centralization_bridge
    {G : Type u} [Group G] [Finite G]
    (t : G) (htInv : IsInvolution t)
    {N X : Subgroup G}
    (htN : t ∈ N)
    (hX : X ≤ oddCoreOf N ⊓ fittingSubgroupOf N)
    (htO2 : t ∈ twoCoreOf (Subgroup.normalizer (X : Set G))) :
    Subgroup.zpowers t ≤ Subgroup.centralizer
      (oddCoreOf N ⊓ fittingSubgroupOf N : Set G) := by
  exact lemma_2_9_centralizes_oddCore_inf_fitting_of_mem_twoCore
    t htInv N X hX htN htO2

public theorem lemma_2_9
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hlocal : Lemma29Hypothesis c)
    {V N : Subgroup G}
    (hVN : V ≤ N) (htV : c.t ∈ V) (hV : IsKleinFour V)
    (hNtop : N ≠ ⊤) (hVS : V ≤ (c.S : Subgroup G)) :
    V ⊓ twoCoreOf N ≠ ⊥ ∨ V ⊓ componentLayerOf N ≠ ⊥ := by
  classical
  have _htS : c.t ∈ (c.S : Subgroup G) := hVS htV
  by_contra hconcl
  have hV2 : V ⊓ twoCoreOf N = ⊥ := by
    by_contra hne
    exact hconcl (Or.inl hne)
  have hVE : V ⊓ componentLayerOf N = ⊥ := by
    by_contra hne
    exact hconcl (Or.inr hne)
  let A : Subgroup G := oddCoreOf N ⊓ fittingSubgroupOf N
  have hfaith := dGroup_faithfulness_bridge hmin N V hNtop hV hVN hV2 hVE
  rcases lemma_2_9_two_involution_bridge c hVN htV hV hfaith with
    ⟨v, X, hvV, hvne, _hvt, hXne, hXleA, hXodd, hXcomm, hvX⟩
  have hvO2 :=
    transport_local_to_pair hmin c hlocal hV htV hvV hvne
      hXne hXodd hXcomm hvX
  have hv2 : v ^ 2 = 1 := by
    simpa [pow_two] using
      (congrArg Subtype.val (IsKleinFour.mul_self (⟨v, hvV⟩ : ↥V)))
  have hvInv : IsInvolution v := ⟨hvne, hv2⟩
  have hvN : v ∈ N := hVN hvV
  have hvCentA : Subgroup.zpowers v ≤ Subgroup.centralizer (A : Set G) :=
    lemma_2_9_centralization_bridge v hvInv hvN hXleA hvO2
  have hvCentA' : v ∈ Subgroup.centralizer (A : Set G) :=
    hvCentA (Subgroup.mem_zpowers v)
  have hvVcent : v ∈ V ⊓ Subgroup.centralizer
      ((oddCoreOf N ⊓ fittingSubgroupOf N : Subgroup G) : Set G) :=
    ⟨hvV, by simpa [A] using hvCentA'⟩
  have hvbot : v ∈ (⊥ : Subgroup G) := by
    rw [hfaith] at hvVcent
    exact hvVcent
  exact hvne (by simpa using hvbot)

end

end CFSG.GorensteinWalter
