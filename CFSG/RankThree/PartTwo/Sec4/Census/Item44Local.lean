module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Basic
public import CFSG.GroupTheory.FrattiniQuotient
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X]

structure CriticalAt (q : ℕ) (D : Subgroup X) : Prop where
  normal : D.Normal
  le : D ≤ pCore q X
  ne_bot : D ≠ ⊥
  exp : ∀ x ∈ D, x ^ q = 1
  comm : ∀ a ∈ D, ∀ b ∈ pCore q X, ⁅a, b⁆ ∈ D ∧ ∀ d ∈ D, ⁅a, b⁆ * d = d * ⁅a, b⁆
  fix : ∀ y : X, (∀ d ∈ D, y * d * y⁻¹ = d) →
    ∃ k : ℕ, ∀ x ∈ pCore q X, y ^ (q ^ k) * x * (y ^ (q ^ k))⁻¹ = x

theorem exists_criticalAt {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2) (hP : pCore q X ≠ ⊥) :
    ∃ D : Subgroup X, CriticalAt q D := by
  set P := pCore q X with hPdef
  have : P.Normal := pCore_normal
  have hPq : IsPGroup q P := pCore_isPGroup
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP
  obtain ⟨D₀, hD₀c, hD₀1, hD₀comm, hD₀exp, hD₀fix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hq2 hPq
  refine ⟨D₀.map P.subtype, ⟨inferInstance, Subgroup.map_subtype_le _, fun h => hD₀1 ?_, ?_, ?_,
    ?_⟩⟩
  · exact (Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).mp h
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.subtype_apply, ← Subgroup.coe_pow, hD₀exp x hx, Subgroup.coe_one]
  · rintro _ ⟨a, ha, rfl⟩ b hb
    have h1 : ⁅a, (⟨b, hb⟩ : P)⁆ ∈ ⁅D₀, (⊤ : Subgroup P)⁆ :=
      Subgroup.commutator_mem_commutator ha (Subgroup.mem_top _)
    obtain ⟨h2, h3⟩ := hD₀comm h1
    refine ⟨⟨_, h2, rfl⟩, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    have h4 := Subgroup.mem_centralizer_iff.mp h3 d hd
    exact (congrArg Subtype.val h4).symm
  · intro y hy
    set σ : MulAut P := MulAut.conjNormal y with hσ
    have hσfix : σ ∈ fixingSubgroup (MulAut P) (D₀ : Set P) := by
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      exact hy _ ⟨d, hd, rfl⟩
    obtain ⟨k, hk⟩ := hD₀fix ⟨σ, hσfix⟩
    refine ⟨k, fun x hx => ?_⟩
    have h1 : σ ^ (q ^ k) = 1 := congrArg Subtype.val hk
    have h2 := congrArg (fun τ : MulAut P => ((τ ⟨x, hx⟩ : P) : X)) h1
    simp only [hσ, ← map_pow, MulAut.conjNormal_apply, MulAut.one_apply] at h2
    exact h2

namespace CriticalAt

variable {q : ℕ} {D : Subgroup X}

theorem centralizes_of_coprime (h : CriticalAt q D) {y : X} (hy : Nat.Coprime (orderOf y) q)
    (hyD : ∀ d ∈ D, y * d * y⁻¹ = d) : ∀ x ∈ pCore q X, y * x * y⁻¹ = x := by
  obtain ⟨k, hk⟩ := h.fix y hyD
  have hz : y ^ (q ^ k) ∈ Subgroup.centralizer (pCore q X : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => by
      have := hk x hx
      calc x * y ^ q ^ k = y ^ q ^ k * x * (y ^ q ^ k)⁻¹ * y ^ q ^ k := by rw [this]
        _ = y ^ q ^ k * x := by group
  have hyz : y ∈ Subgroup.centralizer (pCore q X : Set X) := by
    rcases (show orderOf y = 1 ∨ 1 < orderOf y from by
      have := orderOf_pos y
      omega) with h1 | h1
    · rw [orderOf_eq_one_iff] at h1
      rw [h1]
      exact Subgroup.one_mem _
    · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
        (Nat.Coprime.pow_left k hy.symm) h1
      have hy' : (y ^ q ^ k) ^ m = y := by
        rw [← pow_mul, ← pow_mod_orderOf, hm, pow_one]
      rw [← hy']
      exact Subgroup.pow_mem _ hz m
  intro x hx
  have := Subgroup.mem_centralizer_iff.mp hyz x hx
  calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [this]
    _ = x := by group

@[expose] noncomputable def conjD (h : CriticalAt q D) : X →* MulAut D :=
  have := h.normal
  MulAut.conjNormal

omit [Finite X] in
theorem conjD_apply (h : CriticalAt q D) (y : X) (d : D) :
    ((h.conjD y d : D) : X) = y * d * y⁻¹ := by
  have := h.normal
  rfl

theorem eq_one_of_isPGroup_of_coprime {M : Type*} [Group M] {σ : M} (hσ : ∃ k : ℕ, σ ^ q ^ k = 1)
    {n : ℕ} (hn : σ ^ n = 1) (hcop : Nat.Coprime n q) : σ = 1 := by
  obtain ⟨k, hk⟩ := hσ
  have h1 : orderOf σ ∣ q ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf σ ∣ n := orderOf_dvd_of_pow_eq_one hn
  have h3 : orderOf σ ∣ Nat.gcd n (q ^ k) := Nat.dvd_gcd h2 h1
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k hcop), Nat.dvd_one,
    orderOf_eq_one_iff] at h3
  exact h3

@[expose] noncomputable def frattiniAct (h : CriticalAt q D) : X →* MulAut (D ⧸ frattini D) :=
  (quotientAutomorphism (frattini D)).comp h.conjD

@[expose] noncomputable def frattiniKer (h : CriticalAt q D) : Subgroup X := h.frattiniAct.ker

omit [Finite X] in
theorem mem_frattiniKer_iff (h : CriticalAt q D) (y : X) :
    y ∈ h.frattiniKer ↔ h.frattiniAct y = 1 :=
  MonoidHom.mem_ker

omit [Finite X] in
theorem frattiniKer_normal (h : CriticalAt q D) : h.frattiniKer.Normal :=
  MonoidHom.normal_ker _

theorem conjD_isPGroup_of_mem_frattiniKer [hq : Fact q.Prime] (h : CriticalAt q D) {y : X}
    (hy : y ∈ h.frattiniKer) : ∃ k : ℕ, h.conjD y ^ q ^ k = 1 := by
  have hD : IsPGroup q D := pCore_isPGroup.to_le h.le
  obtain ⟨-, hker⟩ := CFSG.GroupTheory.frattini_automorphism_kernel hD
  obtain ⟨k, hk⟩ := hker ⟨h.conjD y, hy⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem centralizes_D_of_mem_frattiniKer [Fact q.Prime] (h : CriticalAt q D) {y : X}
    (hy : y ∈ h.frattiniKer) (hcop : Nat.Coprime (orderOf y) q) : ∀ d ∈ D, y * d * y⁻¹ = d := by
  have h1 : h.conjD y = 1 := eq_one_of_isPGroup_of_coprime (h.conjD_isPGroup_of_mem_frattiniKer hy)
    (by rw [← map_pow, pow_orderOf_eq_one, map_one]) hcop
  intro d hd
  have := congrArg (fun σ : MulAut D => ((σ ⟨d, hd⟩ : D) : X)) h1
  simpa only [h.conjD_apply, MulAut.one_apply] using this

theorem centralizes_of_mem_frattiniKer [Fact q.Prime] (h : CriticalAt q D) {y : X}
    (hy : y ∈ h.frattiniKer) (hcop : Nat.Coprime (orderOf y) q) :
    ∀ x ∈ pCore q X, y * x * y⁻¹ = x :=
  h.centralizes_of_coprime hcop (h.centralizes_D_of_mem_frattiniKer hy hcop)

variable [Group.IsPerfect X] {K : Subgroup X} [K.Normal] [IsSimpleGroup (X ⧸ K)]

theorem centralizer_le [Fact q.Prime] (h : CriticalAt q D) (hK : Group.IsSolvable K)
    (hPK : Subgroup.centralizer (pCore q X : Set X) ≤ K) :
    Subgroup.centralizer (D : Set X) ≤ K := by
  have := h.normal
  have : (pCore q X).Normal := pCore_normal
  set T := Subgroup.centralizer (D : Set X) with hT
  set χ : X →* MulAut (pCore q X) := MulAut.conjNormal
  set g : T →* (χ.comp T.subtype).range := (χ.comp T.subtype).rangeRestrict
  have hpg : IsPGroup q (χ.comp T.subtype).range := by
    rintro ⟨_, ⟨t, rfl⟩⟩
    obtain ⟨k, hk⟩ := h.fix t (fun d hd => by
      have := Subgroup.mem_centralizer_iff.mp t.2 d hd
      calc (t : X) * d * (t : X)⁻¹ = d * t * (t : X)⁻¹ := by rw [this]
        _ = d := by group)
    refine ⟨k, Subtype.ext ?_⟩
    ext x
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, MonoidHom.comp_apply,
      Subgroup.coe_subtype, ← map_pow, MulAut.one_apply]
    exact hk x x.2
  have : Group.IsSolvable (χ.comp T.subtype).range := by
    have := hpg.isNilpotent
    infer_instance
  have hKT : Group.IsSolvable (K ⊓ T : Subgroup X) := by
    have := hK
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left : K ⊓ T ≤ K))
  have hker : g.ker ≤ (Subgroup.inclusion (inf_le_right : K ⊓ T ≤ T)).range := by
    intro t ht
    have ht' : χ t = 1 := by
      have := congrArg Subtype.val ((MonoidHom.mem_ker).mp ht)
      exact this
    have htP : (t : X) ∈ Subgroup.centralizer (pCore q X : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun x hx => by
        have := congrArg (fun σ : MulAut (pCore q X) => ((σ ⟨x, hx⟩ : pCore q X) : X)) ht'
        change (t : X) * x * (t : X)⁻¹ = x at this
        calc x * t = (t : X) * x * (t : X)⁻¹ * t := by rw [this]
          _ = t * x := by group
    exact ⟨⟨t, hPK htP, t.2⟩, rfl⟩
  have hTsol : Group.IsSolvable T := Group.isSolvable_of_ker_le_range _ g hker
  exact le_of_isSolvable_of_normal inferInstance hTsol

theorem frattiniKer_le [Fact q.Prime] (h : CriticalAt q D) (hK : Group.IsSolvable K)
    (hPK : Subgroup.centralizer (pCore q X : Set X) ≤ K) : h.frattiniKer ≤ K := by
  have hCD := h.centralizer_le hK hPK
  set N := h.frattiniKer
  have hN : N.Normal := MonoidHom.normal_ker _
  set g : N →* (h.conjD.comp N.subtype).range := (h.conjD.comp N.subtype).rangeRestrict
  have hpg : IsPGroup q (h.conjD.comp N.subtype).range := by
    rintro ⟨_, ⟨t, rfl⟩⟩
    obtain ⟨k, hk⟩ := h.conjD_isPGroup_of_mem_frattiniKer t.2
    exact ⟨k, Subtype.ext hk⟩
  have : Group.IsSolvable (h.conjD.comp N.subtype).range := by
    have := hpg.isNilpotent
    infer_instance
  have hKN : Group.IsSolvable (K ⊓ N : Subgroup X) := by
    have := hK
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left : K ⊓ N ≤ K))
  have hker : g.ker ≤ (Subgroup.inclusion (inf_le_right : K ⊓ N ≤ N)).range := by
    intro t ht
    have ht' : h.conjD t = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).mp ht)
    have htD : (t : X) ∈ Subgroup.centralizer (D : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun d hd => by
        have := congrArg (fun σ : MulAut D => ((σ ⟨d, hd⟩ : D) : X)) ht'
        simp only [h.conjD_apply, MulAut.one_apply] at this
        calc d * t = (t : X) * d * (t : X)⁻¹ * t := by rw [this]
          _ = t * d := by group
    exact ⟨⟨t, hCD htD, t.2⟩, rfl⟩
  have hNsol : Group.IsSolvable N := Group.isSolvable_of_ker_le_range _ g hker
  exact le_of_isSolvable_of_normal hN hNsol

end CriticalAt

end CFSG.RankThree.PartTwo.Sec4.Census
