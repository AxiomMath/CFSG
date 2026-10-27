module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SecMod
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def secCentPre (D P I : Subgroup G) (hPI : ∀ p ∈ P, ∀ i ∈ I, p * i * p⁻¹ ∈ I) :
    Subgroup G where
  carrier := {p | p ∈ P ∧ ∀ d ∈ D, ⁅d, p⁆ ∈ I}
  mul_mem' := by
    rintro a b ⟨ha, had⟩ ⟨hb, hbd⟩
    refine ⟨P.mul_mem ha hb, fun d hd => ?_⟩
    have e : ⁅d, a * b⁆ = ⁅d, a⁆ * (a * ⁅d, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact I.mul_mem (had d hd) (hPI a ha _ (hbd d hd))
  one_mem' := ⟨P.one_mem, fun d _ => by
    rw [commutatorElement_one_right]
    exact I.one_mem⟩
  inv_mem' := by
    rintro a ⟨ha, had⟩
    refine ⟨P.inv_mem ha, fun d hd => ?_⟩
    have e : ⁅d, a⁻¹⁆ = (a⁻¹ * ⁅d, a⁆ * a⁻¹⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact I.inv_mem (hPI a⁻¹ (P.inv_mem ha) _ (had d hd))

theorem secCentPre_conj_mem {D P I : Subgroup G} {hPI : ∀ p ∈ P, ∀ i ∈ I, p * i * p⁻¹ ∈ I}
    {r : G} (hrD : ∀ d ∈ D, r⁻¹ * d * r ∈ D) (hrP : ∀ p ∈ P, r * p * r⁻¹ ∈ P)
    (hrI : ∀ i ∈ I, r * i * r⁻¹ ∈ I) {p : G} (hp : p ∈ secCentPre D P I hPI) :
    r * p * r⁻¹ ∈ secCentPre D P I hPI := by
  refine ⟨hrP p hp.1, fun d hd => ?_⟩
  have e : ⁅d, r * p * r⁻¹⁆ = r * ⁅r⁻¹ * d * r, p⁆ * r⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact hrI _ (hp.2 _ (hrD d hd))

theorem exists_fixed_sec_of_isPGroup [Finite G] {D P I : Subgroup G} (hD : IsPGroup 2 ↥D)
    (hsec : SecHyp D P I) (hIP : I < P) : ∃ y ∈ P, y ∉ I ∧ ∀ d ∈ D, ⁅d, y⁆ ∈ I := by
  classical
  obtain ⟨Md, iA, iD, κ, hκ⟩ := exists_sectionModule hsec
  haveI : Finite Md := hκ.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, hpP, hpI⟩ := SetLike.exists_of_lt hIP
  have ha0 : Multiplicative.toAdd (κ ⟨p, hpP⟩) ≠ 0 := by
    intro h
    apply hpI
    refine (hκ.ker ⟨p, hpP⟩).mp ?_
    rw [← ofAdd_toAdd (κ ⟨p, hpP⟩), h, ofAdd_zero]
  have hev : 2 ∣ Nat.card Md := by
    have ho : addOrderOf (Multiplicative.toAdd (κ ⟨p, hpP⟩)) = 2 :=
      addOrderOf_eq_prime (by rw [two_nsmul]; exact hκ.two _) ha0
    rw [← ho]
    exact addOrderOf_dvd_natCard _
  have h0 : (0 : Md) ∈ MulAction.fixedPoints ↥D Md := fun d => smul_zero d
  obtain ⟨a, ha, hne⟩ := hD.exists_fixed_point_of_prime_dvd_card_of_fixed_point Md hev h0
  obtain ⟨y, hy⟩ := hκ.surj (Multiplicative.ofAdd a)
  refine ⟨y, y.2, fun hyI => hne ?_, fun d hd => ?_⟩
  · have h1 : κ y = 1 := (hκ.ker y).mpr hyI
    rw [hy] at h1
    exact (ofAdd_eq_one.mp h1).symm
  · have hact := hκ.act ⟨d, hd⟩ y ⟨d * y * d⁻¹, hsec.normP d hd y y.2⟩ rfl
    have hfix : (⟨d, hd⟩ : ↥D) • a = a := ha ⟨d, hd⟩
    rw [hy, toAdd_ofAdd, hfix, ← hy] at hact
    have h2 := (hκ.eq_iff _ y).mp hact
    simpa [commutatorElement_def] using h2

@[expose] def O2NormPre (M Q Z Z0 : Subgroup G) [(Q.subgroupOf M).Normal] : Subgroup G :=
  ((((pCore 2 ↥(MbarPrime M Q Z Z0)).map (MbarPrime M Q Z Z0).subtype).map
      (bar M Q (H0 M Z)).subtype).comap (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype

section O2NormPre

variable {M Q Z Z0 : Subgroup G} [(Q.subgroupOf M).Normal]

theorem mem_O2NormPre {x : G} :
    x ∈ O2NormPre M Q Z Z0 ↔ ∃ hx : x ∈ M, ∃ y ∈ pCore 2 ↥(MbarPrime M Q Z Z0),
      ((y : Hbar M Q Z) : Mbar M Q) = QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hx⟩ := by
  constructor
  · rintro ⟨⟨x, hx⟩, hmem, rfl⟩
    obtain ⟨y', hy', hy'eq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hmem)
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hy'
    exact ⟨hx, y, hy, hy'eq⟩
  · rintro ⟨hx, y, hy, hyx⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr
      ⟨(y : Hbar M Q Z), Subgroup.mem_map.mpr ⟨y, hy, rfl⟩, hyx⟩), rfl⟩

theorem Q_le_O2NormPre (hQM : Q ≤ M) : Q ≤ O2NormPre M Q Z Z0 := by
  intro x hx
  refine mem_O2NormPre.mpr ⟨hQM hx, 1, Subgroup.one_mem _, ?_⟩
  symm
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hx)

theorem O2NormPre_le_NormH0 (hQN : Q ≤ NormH0 M Z Z0) : O2NormPre M Q Z Z0 ≤ NormH0 M Z Z0 := by
  intro x hx
  obtain ⟨hxM, y, -, hyx⟩ := mem_O2NormPre.mp hx
  have hyK : ((y : Hbar M Q Z) : Mbar M Q) ∈ bar M Q (NormH0 M Z Z0) :=
    Subgroup.mem_subgroupOf.mp y.2
  obtain ⟨x₀, hx₀, hx₀y⟩ := Subgroup.mem_map.mp hyK
  rw [hyx] at hx₀y
  have hq : (x₀ : G)⁻¹ * x ∈ Q := by
    have h1 := QuotientGroup.eq.mp hx₀y
    exact Subgroup.mem_subgroupOf.mp h1
  have e : x = (x₀ : G) * ((x₀ : G)⁻¹ * x) := by group
  rw [e]
  exact (NormH0 M Z Z0).mul_mem (Subgroup.mem_subgroupOf.mp hx₀) (hQN hq)

theorem isPGroup_O2NormPre (hQ : IsPGroup 2 ↥Q) : IsPGroup 2 ↥(O2NormPre M Q Z Z0) := by
  rintro ⟨x, hx⟩
  obtain ⟨hxM, y, hy, hyx⟩ := mem_O2NormPre.mp hx
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := ↥(MbarPrime M Q Z Z0))) ⟨y, hy⟩
  have hyk : y ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hxk : (QuotientGroup.mk' (Q.subgroupOf M) (⟨x, hxM⟩ ^ (2 ^ k)) : Mbar M Q) = 1 := by
    rw [map_pow, ← hyx]
    have := congrArg (fun z : ↥(MbarPrime M Q Z Z0) => ((z : Hbar M Q Z) : Mbar M Q)) hyk
    simpa using this
  have hxQ : x ^ (2 ^ k) ∈ Q := by
    have h1 := (QuotientGroup.eq_one_iff _).mp hxk
    simpa using Subgroup.mem_subgroupOf.mp h1
  obtain ⟨j, hj⟩ := hQ ⟨x ^ (2 ^ k), hxQ⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  have hj' : (x ^ (2 ^ k)) ^ (2 ^ j) = 1 := congrArg Subtype.val hj
  show x ^ (2 ^ (k + j)) = 1
  rw [pow_add, pow_mul]
  exact hj'

theorem conj_mem_O2NormPre {g : G} (hg : g ∈ NormH0 M Z Z0) {x : G}
    (hx : x ∈ O2NormPre M Q Z Z0) : g * x * g⁻¹ ∈ O2NormPre M Q Z Z0 := by
  obtain ⟨hxM, y, hy, hyx⟩ := mem_O2NormPre.mp hx
  have hgM : g ∈ M := hg.1.1
  set gM : ↥M := ⟨g, hgM⟩ with hgMdef
  have hgH : QuotientGroup.mk' (Q.subgroupOf M) gM ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨gM, Subgroup.mem_subgroupOf.mpr hg.1, rfl⟩
  have hgK : QuotientGroup.mk' (Q.subgroupOf M) gM ∈ bar M Q (NormH0 M Z Z0) :=
    Subgroup.mem_map.mpr ⟨gM, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  set g' : ↥(MbarPrime M Q Z Z0) :=
    ⟨⟨QuotientGroup.mk' (Q.subgroupOf M) gM, hgH⟩, Subgroup.mem_subgroupOf.mpr hgK⟩ with hg'
  have hy' : g' * y * g'⁻¹ ∈ pCore 2 ↥(MbarPrime M Q Z Z0) :=
    (pCore_normal (p := 2) (G := ↥(MbarPrime M Q Z Z0))).conj_mem y hy g'
  have hgx : g * x * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM hxM) (M.inv_mem hgM)
  refine mem_O2NormPre.mpr ⟨hgx, g' * y * g'⁻¹, hy', ?_⟩
  have e : (⟨g * x * g⁻¹, hgx⟩ : ↥M) = gM * ⟨x, hxM⟩ * gM⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, ← hyx]
  rfl

end O2NormPre

end CFSG.RankThree.GF2n.Stroth80
