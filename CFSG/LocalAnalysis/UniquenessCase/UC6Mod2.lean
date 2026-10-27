module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Mod
public import CFSG.LocalAnalysis.UniquenessCase.UC6S29

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped IsMulCommutative Pointwise

section Sylow

variable {G : Type} [Group G] [Finite G]

@[expose, instance_reducible] def conjMDMA_uc6 {Z U : Subgroup G} (h : Z ≤ normalizer (U : Set G)) :
    MulDistribMulAction ↥Z ↥U where
  smul z u := ⟨(z : G) * u * (z : G)⁻¹, (mem_normalizer_iff.1 (h z.2) u).1 u.2⟩
  one_smul u := Subtype.ext (by
    show (1 : G) * u * (1 : G)⁻¹ = u
    simp)
  mul_smul a b u := Subtype.ext (by
    show ((a * b : ↥Z) : G) * u * ((a * b : ↥Z) : G)⁻¹ = (a : G) * ((b : G) * u * (b : G)⁻¹) *
      (a : G)⁻¹
    simp [mul_assoc])
  smul_mul z u v := Subtype.ext (by
    show (z : G) * (u * v) * (z : G)⁻¹ = ((z : G) * u * (z : G)⁻¹) * ((z : G) * v * (z : G)⁻¹)
    group)
  smul_one z := Subtype.ext (by
    show (z : G) * 1 * (z : G)⁻¹ = 1
    simp)

theorem exists_invariant_sylow_uc6 {r : ℕ} [Fact r.Prime] (p : ℕ) [Fact p.Prime] {U Z : Subgroup G}
    (hZU : Z ≤ normalizer (U : Set G)) (hZ : IsPGroup r Z) (hcop : ¬ r ∣ Nat.card U) :
    ∃ P : Subgroup G, IsSylowOf p P U ∧ Z ≤ normalizer (P : Set G) := by
  letI := conjMDMA_uc6 hZU
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow p ↥U))
  haveI : Finite (Sylow p ↥U) := inferInstance
  have hdvd : Nat.card (Sylow p ↥U) ∣ Nat.card U := by
    rw [Sylow.card_eq_index_normalizer S₀]
    exact Subgroup.index_dvd_card _
  have hn : ¬ r ∣ Nat.card (Sylow p ↥U) := fun h => hcop (h.trans hdvd)
  obtain ⟨S, hS⟩ := hZ.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p ↥U) hn
  refine ⟨(S : Subgroup ↥U).map U.subtype, ⟨S, rfl⟩, fun z hz => ?_⟩
  refine mem_normalizer_of_forward_uc6 ?_
  rintro _ ⟨s, hs, rfl⟩
  have hfix : (⟨z, hz⟩ : ↥Z) • S = S := MulAction.mem_fixedPoints.1 hS ⟨z, hz⟩
  have hmem : (⟨z, hz⟩ : ↥Z) • s ∈ ((⟨z, hz⟩ : ↥Z) • S : Sylow p ↥U) := by
    show _ ∈ ((⟨z, hz⟩ : ↥Z) • (S : Subgroup ↥U))
    exact Subgroup.smul_mem_pointwise_smul s _ _ hs
  rw [hfix] at hmem
  exact ⟨_, hmem, rfl⟩

end Sylow

section OmegaCenter

variable {G : Type} [Group G] [Finite G]

@[expose] def omegaCenter (p : ℕ) (P : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ P ∧ x ^ p = 1 ∧ ∀ y ∈ P, x * y = y * x}
  mul_mem' {a b} ha hb := by
    refine ⟨P.mul_mem ha.1 hb.1, ?_, fun y hy => ?_⟩
    · have hab : Commute a b := (hb.2.2 a ha.1).symm
      rw [hab.mul_pow, ha.2.1, hb.2.1, mul_one]
    · calc a * b * y = a * (b * y) := mul_assoc _ _ _
        _ = a * (y * b) := by rw [hb.2.2 y hy]
        _ = (a * y) * b := (mul_assoc _ _ _).symm
        _ = (y * a) * b := by rw [ha.2.2 y hy]
        _ = y * (a * b) := mul_assoc _ _ _
  one_mem' := ⟨P.one_mem, one_pow _, fun y _ => by simp⟩
  inv_mem' {a} ha := by
    refine ⟨P.inv_mem ha.1, by rw [inv_pow, ha.2.1, inv_one], fun y hy => ?_⟩
    have h : Commute a y := ha.2.2 y hy
    exact (Commute.inv_left h).eq

theorem omegaCenter_le (p : ℕ) (P : Subgroup G) : omegaCenter p P ≤ P := fun _ hx => hx.1

theorem isElemAbelian_omegaCenter (p : ℕ) (P : Subgroup G) :
    CFSG.Open.IsElemAbelian p (omegaCenter p P) :=
  ⟨⟨⟨fun a b => Subtype.ext (b.2.2.2 a a.2.1).symm⟩⟩, fun x hx => hx.2.1⟩

theorem normalizer_le_normalizer_omegaCenter (p : ℕ) (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer (omegaCenter p P : Set G) := by
  intro n hn
  refine mem_normalizer_of_forward_uc6 ?_
  intro x hx
  have hn' : n⁻¹ ∈ normalizer (P : Set G) := inv_mem hn
  refine ⟨(mem_normalizer_iff.1 hn x).1 hx.1, ?_, fun y hy => ?_⟩
  · have := conj_pow (a := n) (b := x) (i := p)
    rw [hx.2.1] at this
    simpa using this
  · have hy' : n⁻¹ * y * n ∈ P := by
      have := (mem_normalizer_iff.1 hn' y).1 hy
      simpa using this
    have h1 := hx.2.2 _ hy'
    calc n * x * n⁻¹ * y = n * (x * (n⁻¹ * y * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * y * n) * x) * n⁻¹ := by rw [h1]
      _ = y * (n * x * n⁻¹) := by group

theorem omegaCenter_ne_bot {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P)
    (hP1 : P ≠ ⊥) : omegaCenter p P ≠ ⊥ := by
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hP1
  haveI : Nontrivial (Subgroup.center ↥P) := hP.center_nontrivial
  have hcp : IsPGroup p (Subgroup.center ↥P) := hP.to_subgroup _
  obtain ⟨n, hn, hcard⟩ := (hcp.nontrivial_iff_card).1 inferInstance
  have hdvd : p ∣ Nat.card (Subgroup.center ↥P) := by
    rw [hcard]
    exact dvd_pow_self p hn.ne'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  intro hbot
  have hxmem : ((x : ↥P) : G) ∈ omegaCenter p P := by
    refine ⟨(x : ↥P).2, ?_, fun y hy => ?_⟩
    · have h0 : x ^ p = 1 := by
        have := pow_orderOf_eq_one x
        rwa [hx] at this
      have h1 : (((x ^ p : ↥(Subgroup.center ↥P)) : ↥P) : G) = 1 := by
        rw [h0]
        rfl
      simpa using h1
    · have := Subgroup.mem_center_iff.1 x.2 ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
  rw [hbot, Subgroup.mem_bot] at hxmem
  have h1 : (x : ↥P) = 1 := Subtype.ext hxmem
  have hx1 : x = 1 := Subtype.ext h1
  rw [hx1, orderOf_one] at hx
  exact (Fact.out : p.Prime).ne_one hx.symm

end OmegaCenter

section Fpf

variable {G : Type} [Group G] [Finite G]

theorem commutator_eq_of_fixedPointFree_uc6 {Z Q : Subgroup G} {z₀ : G} (hZ : Z = zpowers z₀)
    (hQab : IsMulCommutative ↥Q) (hZQ : Z ≤ normalizer (Q : Set G))
    (hfix : ∀ q ∈ Q, (∀ z ∈ Z, z * q = q * z) → q = 1) : ⁅Z, Q⁆ = Q := by
  have hz0 : z₀ ∈ Z := hZ ▸ Subgroup.mem_zpowers z₀
  have hconj : ∀ q ∈ Q, z₀ * q * z₀⁻¹ ∈ Q := fun q hq => (mem_normalizer_iff.1 (hZQ hz0) q).1 hq
  have hcomm : ∀ q : ↥Q, z₀ * (q : G) * z₀⁻¹ * (q : G)⁻¹ ∈ Q := fun q =>
    Q.mul_mem (hconj q q.2) (Q.inv_mem q.2)
  let f : ↥Q → ↥Q := fun q => ⟨z₀ * (q : G) * z₀⁻¹ * (q : G)⁻¹, hcomm q⟩
  have hf_mul : ∀ a b : ↥Q, f (a * b) = f a * f b := by
    intro a b
    apply Subtype.ext
    show z₀ * ((a : G) * b) * z₀⁻¹ * ((a : G) * b)⁻¹ =
      (z₀ * (a : G) * z₀⁻¹ * (a : G)⁻¹) * (z₀ * (b : G) * z₀⁻¹ * (b : G)⁻¹)
    have hc : (a : G) * (z₀ * (b : G) * z₀⁻¹ * (b : G)⁻¹) =
        (z₀ * (b : G) * z₀⁻¹ * (b : G)⁻¹) * (a : G) :=
      congrArg Subtype.val (hQab.is_comm.comm a ⟨_, hcomm b⟩)
    have hc' : (z₀ * (b : G) * z₀⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ =
        (a : G)⁻¹ * (z₀ * (b : G) * z₀⁻¹ * (b : G)⁻¹) := by
      calc (z₀ * (b : G) * z₀⁻¹ * (b : G)⁻¹) * (a : G)⁻¹
          = (a : G)⁻¹ * ((a : G) * (z₀ * (b : G) * z₀⁻¹ * (b : G)⁻¹)) * (a : G)⁻¹ := by group
        _ = (a : G)⁻¹ * ((z₀ * (b : G) * z₀⁻¹ * (b : G)⁻¹) * (a : G)) * (a : G)⁻¹ := by rw [hc]
        _ = (a : G)⁻¹ * (z₀ * (b : G) * z₀⁻¹ * (b : G)⁻¹) := by group
    calc z₀ * ((a : G) * b) * z₀⁻¹ * ((a : G) * b)⁻¹
        = (z₀ * (a : G) * z₀⁻¹) * ((z₀ * (b : G) * z₀⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
      _ = (z₀ * (a : G) * z₀⁻¹) * ((a : G)⁻¹ * (z₀ * (b : G) * z₀⁻¹ * (b : G)⁻¹)) := by rw [hc']
      _ = _ := by group
  let fh : ↥Q →* ↥Q := MonoidHom.mk' f hf_mul
  have hinj : Function.Injective fh := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    rw [MonoidHom.mem_ker] at hq
    have h1 : z₀ * (q : G) * z₀⁻¹ * (q : G)⁻¹ = 1 := congrArg Subtype.val hq
    have h2 : z₀ * (q : G) = (q : G) * z₀ := by
      have h3 : z₀ * (q : G) * z₀⁻¹ = (q : G) := mul_inv_eq_one.1 h1
      calc z₀ * (q : G) = (z₀ * (q : G) * z₀⁻¹) * z₀ := by group
        _ = (q : G) * z₀ := by rw [h3]
    have hqz : ∀ z ∈ Z, z * (q : G) = (q : G) * z := by
      intro z hz
      rw [hZ, Subgroup.mem_zpowers_iff] at hz
      obtain ⟨k, rfl⟩ := hz
      exact (Commute.zpow_left (show Commute z₀ (q : G) from h2) k).eq
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hfix q q.2 hqz)
  have hsurj : Function.Surjective fh := Finite.injective_iff_surjective.1 hinj
  refine le_antisymm (Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_) fun q hq => ?_
  · have := (mem_normalizer_iff.1 (hZQ hg₁) g₂).1 hg₂
    rw [commutatorElement_def]
    exact Q.mul_mem this (Q.inv_mem hg₂)
  · obtain ⟨q', hq'⟩ := hsurj ⟨q, hq⟩
    have h1 : z₀ * (q' : G) * z₀⁻¹ * (q' : G)⁻¹ = q := congrArg Subtype.val hq'
    rw [← h1, ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator hz0 q'.2

end Fpf

section TransportTwo

open CFSG.RankThree.FFModules (fixSub)

variable {Mg : Type} [Group Mg] [Finite Mg]

theorem k47_transport_two_uc6 (hK : UCK.K47) (hMg : CFSG.Open.IsKGroup Mg)
    (Q₀ : Subgroup Mg) [Q₀.Normal] (hQ₀ : IsPGroup 2 Q₀)
    (hchar : centralizer (Q₀ : Set Mg) ≤ Q₀) {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hq2 : q ≠ 2) (hr2 : r ≠ 2) (hqr : q ≠ r) (D : Subgroup Mg) (hDcard : Nat.card D = r)
    (hfix : Nat.card ↥(Q₀ ⊓ centralizer (D : Set Mg)) ≤ 2) (Q : Subgroup Mg) (hQp : IsPGroup q Q)
    (hQab : IsMulCommutative ↥Q) (hDQ : D ≤ normalizer (Q : Set Mg)) (hcomm : ⁅D, Q⁆ = Q) :
    IsCyclic ↥Q := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : IsElementaryAbelian 2 (↥Q₀ ⧸ frattini ↥Q₀) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hQ₀).2.2.2.1
  set ρ := frattiniRep Q₀ with hρ
  set N : Subgroup Mg := ρ.ker with hN
  haveI hNn : N.Normal := MonoidHom.normal_ker ρ
  have hGK : CFSG.Open.IsKGroup (Mg ⧸ N) := hMg.quotient N
  set ρ' : Representation (ZMod 2) (Mg ⧸ N) (Additive (↥Q₀ ⧸ frattini ↥Q₀)) :=
    QuotientGroup.lift N ρ (fun x hx => hx) with hρ'
  have hρ'mk : ∀ g : Mg, ρ' (QuotientGroup.mk' N g) = ρ g := fun g => rfl
  have hinj : Function.Injective ρ' := by
    intro a b hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N b
    rw [hρ'mk, hρ'mk] at hab
    apply QuotientGroup.eq.2
    show a⁻¹ * b ∈ ρ.ker
    rw [MonoidHom.mem_ker, map_mul, ← hab, ← map_mul, inv_mul_cancel, map_one]
  have hDp : IsPGroup r D := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hDcard)
  have hodd : ∀ z : Mg, Odd (orderOf z) → z ∈ N → z = 1 := fun z hz hzN =>
    eq_one_of_odd_of_rep_eq_one_uc6 Q₀ hQ₀ hchar hz hzN
  have hpN : ∀ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup Mg), IsPGroup p P →
      ∀ z ∈ P, z ∈ N → z = 1 := fun p hp hp2 P hP z hz hzN =>
    hodd z (odd_orderOf_of_mem_pGroup_uc6 hp hp2 hP hz) hzN
  set D' : Subgroup (Mg ⧸ N) := D.map (QuotientGroup.mk' N) with hD'
  have hD'card : Nat.card D' = r := by
    have hdvd : Nat.card D' ∣ Nat.card D := Subgroup.card_map_dvd D _
    rw [hDcard] at hdvd
    rcases (Nat.dvd_prime hr).1 hdvd with h1 | h1
    · exfalso
      have hDbot : D' = ⊥ := Subgroup.card_eq_one.1 h1
      obtain ⟨x, hxD, hx1⟩ : ∃ x ∈ D, x ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : Nat.card D = 1 := Subgroup.card_eq_one.2 (eq_bot_iff.2 fun x hx => by
          rw [Subgroup.mem_bot]; exact hcon x hx)
        rw [hDcard] at this
        exact hr.ne_one this
      have hmem : (QuotientGroup.mk' N x) ∈ D' := ⟨x, hxD, rfl⟩
      rw [hDbot, Subgroup.mem_bot] at hmem
      exact hx1 (hpN r hr hr2 D hDp x hxD ((QuotientGroup.eq_one_iff x).1 hmem))
    · exact h1
  have hfD : Module.finrank (ZMod 2) (fixSub ρ' D') ≤ 1 := by
    have h1 := finrank_fixSub_le_uc6 Q₀ hQ₀ hr2 D hDp hfix
    have heq : fixSub ρ' D' = fixSub ρ D := by
      ext v
      constructor
      · intro hv x hx
        have := hv (QuotientGroup.mk' N x) ⟨x, hx, rfl⟩
        rw [hρ'mk] at this
        exact this
      · intro hv d hd
        obtain ⟨x, hx, rfl⟩ := hd
        have := hv x hx
        rw [hρ'mk]
        exact this
    rw [heq]; exact h1
  set Q' : Subgroup (Mg ⧸ N) := Q.map (QuotientGroup.mk' N) with hQ'
  have hQ'p : IsPGroup q Q' := hQp.map _
  have hQ'ab : IsMulCommutative ↥Q' := ⟨⟨fun a b => by
    obtain ⟨a, x, hx, hxa⟩ := a
    obtain ⟨b, y, hy, hyb⟩ := b
    apply Subtype.ext
    show a * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hQab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))⟩⟩
  have hD'Q' : D' ≤ normalizer (Q' : Set (Mg ⧸ N)) := by
    rintro _ ⟨d, hd, rfl⟩
    refine mem_normalizer_of_forward_uc6 ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨d * x * d⁻¹, (mem_normalizer_iff.1 (hDQ hd) x).1 hx, ?_⟩
    simp
  have hcomm' : ⁅D', Q'⁆ = Q' := by
    rw [hD', hQ', ← Subgroup.map_commutator, hcomm]
  have hk := (hK (Mg ⧸ N) hGK (Additive (↥Q₀ ⧸ frattini ↥Q₀)) ρ' hinj q r hq hr hq2 hr2 hqr D'
    hD'card hfD).2 Q' hQ'p hQ'ab hD'Q' hcomm'
  let e : ↥Q →* ↥Q' :=
    { toFun := fun x => ⟨QuotientGroup.mk' N (x : Mg), x, x.2, rfl⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have he : Function.Bijective e := by
    constructor
    · intro a b hab
      have h1 : QuotientGroup.mk' N (a : Mg) = QuotientGroup.mk' N (b : Mg) :=
        congrArg Subtype.val hab
      have h2 : (a : Mg)⁻¹ * (b : Mg) ∈ N := QuotientGroup.eq.1 h1
      have h3 : (a : Mg)⁻¹ * (b : Mg) ∈ Q := Q.mul_mem (Q.inv_mem a.2) b.2
      have h4 := hpN q hq hq2 Q hQp _ h3 h2
      apply Subtype.ext
      exact inv_mul_eq_one.1 h4
    · rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  haveI := hk
  exact isCyclic_of_surjective (MulEquiv.ofBijective e he).symm.toMonoidHom
    (MulEquiv.surjective _)

end TransportTwo

end CFSG.LocalAnalysis.UniquenessCase.UC6
