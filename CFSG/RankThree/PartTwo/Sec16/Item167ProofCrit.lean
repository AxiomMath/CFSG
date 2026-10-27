module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut
public import CFSG.RankThree.PartTwo.KFacts.KP10LinearTwo
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GH74.GLS.Basic
import CFSG.LocalAnalysis.SectionRank.Ccomm.Centralization
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.RankThree.PGroups.SolvableTrivialComplementCore
import CFSG.RankThree.Transfer.Yoshida
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Core
import CFSG.Foundations.SteinbergCAGeneratedCoreNodes
import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.RankThree.PartTwo.Sec4.StatementsCensus

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec16.Crit167

open CFSG CFSG.Open CFSG.SectionRank CFSG.SectionRank.Ccomm Subgroup
open scoped commutatorElement

@[expose] noncomputable def quotPCoreAut (Y : Type*) [Group Y] :
    MulAut Y →* MulAut (Y ⧸ CFSG.pCore 2 Y) where
  toFun σ := QuotientGroup.congr (CFSG.pCore 2 Y) (CFSG.pCore 2 Y) σ (CFSG.pCore_map_iso 2 σ)
  map_one' := by
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]

theorem quotPCoreAut_apply_mk {Y : Type*} [Group Y] (σ : MulAut Y) (y : Y) :
    quotPCoreAut Y σ (y : Y ⧸ CFSG.pCore 2 Y) = ((σ y : Y) : Y ⧸ CFSG.pCore 2 Y) :=
  rfl

section Rep

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem exists_rep {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (Q : Subgroup Γ) [Q.Normal]
    (hQ : IsPGroup r Q) (hrank : CFSG.Open.pRank r Q ≤ 2) :
    ∃ k : ℕ, k ≤ 2 ∧ ∃ φ : Γ →* GL (Fin k) (ZMod r),
      ∀ x : Γ, Nat.Coprime (orderOf x) r → φ x = 1 → x ∈ centralizer (Q : Set Γ) := by
  by_cases hQbot : Q = ⊥
  · refine ⟨0, by omega, 1, fun x _ _ => ?_⟩
    rw [hQbot, mem_centralizer_iff]
    intro h hh
    rw [SetLike.mem_coe, mem_bot] at hh
    rw [hh, one_mul, mul_one]
  have hQnt : Nontrivial Q := (nontrivial_iff_ne_bot Q).2 hQbot
  set α : Γ →* MulAut Q := MulAut.conjNormal with hα
  obtain ⟨D, hDc, -, hDexp, -, -, hker⟩ := supercritical_witness hr2 hQ
  set W := D ⧸ frattini D
  set ρ : Γ →* MulAut W := (frattiniAction D).comp α with hρ
  have hDp : IsPGroup r D := hQ.to_subgroup D
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
  have hDrank : CFSG.Open.pRank r (⊤ : Subgroup D) ≤ 2 := by
    let f : D →* Γ := Q.subtype.comp D.subtype
    have hf : Function.Injective f := Q.subtype_injective.comp D.subtype_injective
    refine (pRank_le_map hr.out.one_lt f hf ⊤).trans ((pRank_mono hr.out.one_lt ?_).trans hrank)
    rintro _ ⟨d, -, rfl⟩
    exact (d : Q).2
  obtain ⟨-, hW2⟩ := rank_two_exponent_prime_order_bound hDp
    (fun x => Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hDexp _ x.2))
    hDrank
  obtain ⟨k, hk⟩ := (hDp.to_quotient (frattini D)).exists_card_eq
  have hk2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hr.out.one_lt).1 (hk ▸ hW2)
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hk
  set ψ := elemAutEquivGL e with hψ
  refine ⟨k, hk2, ψ.toMonoidHom.comp ρ, fun x hx hφ => ?_⟩
  have hρx : ρ x = 1 := by
    apply ψ.injective
    rw [map_one]
    exact hφ
  have hαker : α x ∈ (frattiniAction D).ker := hρx
  have hαx : α x = 1 := by
    obtain ⟨n, hn⟩ := hker ⟨α x, hαker⟩
    have h1 : (α x) ^ r ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h2 : orderOf (α x) ∣ orderOf x := orderOf_map_dvd α x
    have h3 : orderOf (α x) ∣ Nat.gcd (r ^ n) (orderOf x) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) h2
    rw [(Nat.Coprime.pow_left n hx.symm).gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  rw [mem_centralizer_iff]
  intro q hq
  have h := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : Γ)) hαx
  simp only [hα, MulAut.conjNormal_apply, MulAut.one_apply] at h
  calc q * x = x * q * x⁻¹ * x := by rw [h]
    _ = x * q := by group

end Rep

section Complement

variable {T : Type*} [Group T] [Finite T]

omit [Finite T] in
theorem oResidual_two_normal : (CFSG.GH74.GLS.oResidual 2 T).Normal := by
  constructor
  intro n hn g
  unfold CFSG.GH74.GLS.oResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    have h1 : orderOf (g * x * g⁻¹) = orderOf x :=
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    show Nat.Coprime (orderOf (g * x * g⁻¹)) 2
    rw [h1]
    exact hx
  | one => simp
  | mul a b _ _ iha ihb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ iha ihb
  | inv a _ iha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ iha

omit [Finite T] in
theorem oResidual_two_le_of_isPGroup_quotient {N : Subgroup T} [N.Normal]
    (h : IsPGroup 2 (T ⧸ N)) : CFSG.GH74.GLS.oResidual 2 T ≤ N := by
  refine (Subgroup.closure_le N).mpr fun y hy => ?_
  have hy' : Nat.Coprime (orderOf y) 2 := hy
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp h (QuotientGroup.mk y)
  have hd : orderOf (QuotientGroup.mk y : T ⧸ N) ∣ orderOf y :=
    orderOf_map_dvd (QuotientGroup.mk' N) y
  rw [hk] at hd
  have h1 : 2 ^ k = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hy'.symm) hd
  have h2 : (QuotientGroup.mk y : T ⧸ N) = 1 := by
    rw [← orderOf_eq_one_iff, hk, h1]
  exact (QuotientGroup.eq_one_iff y).mp h2

omit [Finite T] in
theorem eq_one_of_mem_oResidual_of_hasNormalPComplement (hT : CFSG.HasNormalPComplement 2 T)
    {t : T} (ht : t ∈ CFSG.GH74.GLS.oResidual 2 T) {n : ℕ} (htn : t ^ 2 ^ n = 1) : t = 1 := by
  obtain ⟨N, hN, hNodd, hq⟩ := hT
  have htN : t ∈ N := oResidual_two_le_of_isPGroup_quotient hq ht
  have h1 : orderOf t ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one htn
  have h2 : orderOf t ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk (ha := htN)]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ n) (Nat.card N) := Nat.Coprime.pow_left n hNodd
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

theorem hasNormalPComplement_two_of_comm (hcomm : ∀ a b : T, a * b = b * a) :
    CFSG.HasNormalPComplement 2 T := by
  have h := KFacts.KP10.hasNormalPComplement_two_of_index_dvd_two (G := T) (C := ⊤)
    (fun a _ b _ => hcomm a b) (by rw [Subgroup.index_top]; exact one_dvd 2)
  exact h

theorem hasNormalPComplement_two_of_le_two {r : ℕ} [Fact r.Prime]
    {k : ℕ} (hk : k ≤ 2) (J : Subgroup (GL (Fin k) (ZMod r))) (hJ : ¬ 3 ∣ Nat.card J) :
    CFSG.HasNormalPComplement 2 J := by
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · exact hasNormalPComplement_two_of_comm fun a b =>
      Subtype.ext (GL_comm_of_le_one (by omega) (a : GL (Fin k) (ZMod r)) b)
  · obtain rfl : k = 2 := by omega
    exact KFacts.KP10.hasNormalPComplement_two_of_not_three_dvd J hJ

theorem rangeRestrict_mem_oResidual {H : Type*} [Group H] {T' : Type*} [Group T'] (f : H →* T')
    {u : H} (hu : u ∈ CFSG.GH74.GLS.oResidual 2 H) :
    f.rangeRestrict u ∈ CFSG.GH74.GLS.oResidual 2 f.range := by
  rw [CFSG.GH74.GLS.oResidual] at hu ⊢
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    have hdvd : orderOf (f.rangeRestrict x) ∣ orderOf x := orderOf_map_dvd _ x
    exact Nat.Coprime.coprime_dvd_left hdvd hx
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

end Complement

section TwoNilpotent

variable {H : Type*} [Group H] [Finite H]

theorem eq_one_of_mem_fittingSubgroup (h2 : CFSG.pCore 2 H = ⊥) {u : H}
    (hu : u ∈ CFSG.fittingSubgroup H) {n : ℕ} (hun : u ^ 2 ^ n = 1) : u = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := CFSG.fittingSubgroup H with hF
  have : Group.IsNilpotent F := (CFSG.LocalCores.fitting_nilpotent (G := H)).1
  set v : F := ⟨u, hu⟩ with hv
  have hvn : v ^ 2 ^ n = 1 := Subtype.ext (by simpa using hun)
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := by
    refine IsPGroup.iff_orderOf.mpr fun g => ?_
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    have h1 : orderOf (g : F) ∣ 2 ^ n := by
      rw [← hk]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hvn, one_zpow]
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact ⟨m, by rw [Subgroup.orderOf_coe] at hm; exact hm⟩
  obtain ⟨S, hS⟩ := hv2.exists_le_sylow
  have hSn : (S : Subgroup F).Normal := inferInstance
  have hSO : (S : Subgroup F) ≤ CFSG.pCore 2 F := le_sSup ⟨hSn, S.isPGroup'⟩
  have hvO : v ∈ CFSG.pCore 2 F := hSO (hS (Subgroup.mem_zpowers v))
  have huO : u ∈ CFSG.pCore 2 H :=
    Sec14.pCore_map_le_pCore F ⟨v, hvO, rfl⟩
  rw [h2, Subgroup.mem_bot] at huO
  exact huO

theorem mem_centralizer_fittingSubgroup {u : H}
    (hu : ∀ r : ℕ, r.Prime → u ∈ centralizer (CFSG.pCore r H : Set H)) :
    u ∈ centralizer (CFSG.fittingSubgroup H : Set H) := by
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore, mem_centralizer_iff]
  intro f hf
  have hle : (⨆ p : (Nat.card H).primeFactors, CFSG.pCore (p : ℕ) H) ≤
      centralizer ({u} : Set H) := by
    refine iSup_le fun p => fun x hx => ?_
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp (hu p (Nat.prime_of_mem_primeFactors p.2)) x hx)
  exact (mem_centralizer_singleton_iff.mp (hle hf))

theorem hasNormalPComplement_two_of_rank [Group.IsSolvable H]
    (h2 : CFSG.pCore 2 H = ⊥) (h3 : ¬ 3 ∣ Nat.card H)
    (hrank : ∀ r : ℕ, r.Prime → 3 < r → CFSG.Open.pRank r (⊤ : Subgroup H) ≤ 2) :
    CFSG.HasNormalPComplement 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := CFSG.GH74.GLS.oResidual 2 H with hUdef
  have hU : ∀ u ∈ U, u ^ 2 = 1 → u = 1 := by
    intro u hu hu2
    have hcen : ∀ r : ℕ, r.Prime → u ∈ centralizer (CFSG.pCore r H : Set H) := by
      intro r hr
      have : Fact r.Prime := ⟨hr⟩
      by_cases hr2 : r = 2
      · subst hr2
        rw [h2, mem_centralizer_iff]
        intro h hh
        rw [SetLike.mem_coe, mem_bot] at hh
        rw [hh, one_mul, mul_one]
      by_cases hr3 : r = 3
      · subst hr3
        have hP1 : CFSG.pCore 3 H = ⊥ := by
          rcases (CFSG.pCore_isPGroup (p := 3) (G := H)).card_eq_or_dvd with h1 | h1
          · exact Subgroup.card_eq_one.mp h1
          · exact absurd (h1.trans (Subgroup.card_subgroup_dvd_card _)) h3
        rw [hP1, mem_centralizer_iff]
        intro h hh
        rw [SetLike.mem_coe, mem_bot] at hh
        rw [hh, one_mul, mul_one]
      have hr5 : 3 < r := by
        have := hr.two_le
        by_contra hle
        interval_cases r <;> simp_all
      have : (CFSG.pCore r H).Normal := CFSG.pCore_normal
      obtain ⟨k, hk, φ, hφ⟩ := exists_rep hr2 (CFSG.pCore r H) CFSG.pCore_isPGroup
        ((CFSG.SectionRank.pRank_mono hr.one_lt le_top).trans (hrank r hr hr5))
      refine hφ u ?_ ?_
      · have h1 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
        exact Nat.Coprime.coprime_dvd_left h1 ((Nat.coprime_primes Nat.prime_two hr).mpr
          (Ne.symm hr2))
      · have hJ3 : ¬ 3 ∣ Nat.card φ.range := fun h =>
          h3 (h.trans (Subgroup.card_dvd_of_surjective (f := φ.rangeRestrict)
            φ.rangeRestrict_surjective))
        have hN := hasNormalPComplement_two_of_le_two hk φ.range hJ3
        have h1 := eq_one_of_mem_oResidual_of_hasNormalPComplement hN
          (rangeRestrict_mem_oResidual φ hu) (n := 1)
          (by rw [pow_one, ← map_pow, hu2, map_one])
        exact congrArg Subtype.val h1
    have hCF : centralizer (CFSG.fittingSubgroup H : Set H) ≤ CFSG.fittingSubgroup H := by
      have h := centralizer_generalizedFitting_le H
      rwa [CFSG.RankThree.PGroups.generalizedFitting_eq_fittingSubgroup_of_isSolvable] at h
    exact eq_one_of_mem_fittingSubgroup h2 (hCF (mem_centralizer_fittingSubgroup hcen)) (n := 1)
      (by rw [pow_one]; exact hu2)
  have hUodd : Nat.Coprime 2 (Nat.card U) := KFacts.KP10.coprime_two_card_of_forall hU
  have : U.Normal := oResidual_two_normal
  exact ⟨U, this, hUodd, CFSG.RankThree.Transfer.isPGroup_quotient_of_oResidual_le U le_rfl⟩

end TwoNilpotent

@[expose] def KS167GL2 : Prop :=
  ∀ r : ℕ, r.Prime → 5 ≤ r → ∀ T B : Subgroup (GL (Fin 2) (ZMod r)),
    ¬ 3 ∣ Nat.card T → IsPGroup 3 B → B ≤ normalizer (T : Set (GL (Fin 2) (ZMod r))) →
      ⁅T, B⁆ = T → IsPGroup r (CFSG.GH74.GLS.oResidual 2 T)

section Residual

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem pRank_map_eq_of_injective {Γ' : Type*} [Group Γ'] [Finite Γ'] {p : ℕ} (hp : p.Prime)
    (f : Γ →* Γ') (hf : Function.Injective f) (P : Subgroup Γ) :
    CFSG.Open.pRank p (P.map f) = CFSG.Open.pRank p P := by
  rw [← CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp,
    ← CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp,
    CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact pRank_top_eq_of_mulEquiv hp.one_lt (P.equivMapOfInjective f hf).symm

end Residual

section ResidualFitting

variable {H : Type*} [Group H] [Finite H]

theorem oResidual_le_fittingSubgroup (hgl : KS167GL2)
    [Group.IsSolvable H] (h2 : CFSG.pCore 2 H = ⊥) (h3 : ¬ 3 ∣ Nat.card H)
    (hrank : ∀ r : ℕ, r.Prime → 3 < r → CFSG.Open.pRank r (⊤ : Subgroup H) ≤ 2)
    {A : Type*} [Group A] [Finite A] (hA : IsPGroup 3 A) (β : A →* MulAut H)
    (hgen : Subgroup.closure {z | ∃ x : H, ∃ a : A, z = x * (β a x)⁻¹} = ⊤) :
    CFSG.GH74.GLS.oResidual 2 H ≤ CFSG.fittingSubgroup H := by
  have hCF : centralizer (CFSG.fittingSubgroup H : Set H) ≤ CFSG.fittingSubgroup H := by
    have h := centralizer_generalizedFitting_le H
    rwa [CFSG.RankThree.PGroups.generalizedFitting_eq_fittingSubgroup_of_isSolvable] at h
  have : (CFSG.GH74.GLS.oResidual 2 H).Normal := oResidual_two_normal
  refine Sec4.Census.le_fittingSubgroup_of_forall_coprime hCF fun r hr y hy hcop x hx => ?_
  have : Fact r.Prime := ⟨hr⟩
  have hx1 : ∀ q : ℕ, q = 2 ∨ q = 3 → q = r → x = 1 := by
    rintro q hq rfl
    rcases hq with rfl | rfl
    · rwa [h2, mem_bot] at hx
    · have hP1 : CFSG.pCore 3 H = ⊥ := by
        rcases (CFSG.pCore_isPGroup (p := 3) (G := H)).card_eq_or_dvd with h1 | h1
        · exact Subgroup.card_eq_one.mp h1
        · exact absurd (h1.trans (Subgroup.card_subgroup_dvd_card _)) h3
      rwa [hP1, mem_bot] at hx
  by_cases hr23 : r = 2 ∨ r = 3
  · rw [hx1 r hr23 rfl, one_mul, mul_one]
  have hr2 : r ≠ 2 := fun h => hr23 (Or.inl h)
  have hr5 : 5 ≤ r := by
    rcases Nat.lt_or_ge r 5 with h | h
    · have h2le := hr.two_le
      interval_cases r
      · exact absurd (Or.inl rfl) hr23
      · exact absurd (Or.inr rfl) hr23
      · exact absurd hr (by decide)
    · exact h
  have : Finite (H ⋊[β] A) :=
    Finite.of_injective (fun x : H ⋊[β] A => (x.left, x.right)) fun x y hxy =>
      SemidirectProduct.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  have hιinj : Function.Injective (SemidirectProduct.inl : H →* H ⋊[β] A) :=
    SemidirectProduct.inl_injective
  have hconj : ∀ (a : A) (n : H), (SemidirectProduct.inl (β a n) : H ⋊[β] A) =
      SemidirectProduct.inr a * SemidirectProduct.inl n * (SemidirectProduct.inr a)⁻¹ :=
    fun a n => by
      have h := SemidirectProduct.inl_aut (φ := β) a n
      rw [map_inv] at h
      exact h
  set P := CFSG.pCore r H with hPdef
  set Q := P.map (SemidirectProduct.inl : H →* H ⋊[β] A) with hQdef
  have hPchar : ∀ (σ : MulAut H), ∀ p ∈ P, σ p ∈ P := fun σ p hp => by
    rw [hPdef, ← CFSG.pCore_map_iso r σ]
    exact ⟨p, hp, rfl⟩
  have hQn : Q.Normal := by
    refine ⟨fun q hq g => ?_⟩
    obtain ⟨p, hp, rfl⟩ := hq
    rw [← SemidirectProduct.inl_left_mul_inr_right g]
    have h1 : SemidirectProduct.inl g.left * SemidirectProduct.inr g.right *
        (SemidirectProduct.inl p : H ⋊[β] A) *
        (SemidirectProduct.inl g.left * SemidirectProduct.inr g.right)⁻¹ =
        SemidirectProduct.inl (g.left * β g.right p * g.left⁻¹) := by
      rw [map_mul, map_mul, map_inv, hconj]
      group
    rw [h1]
    exact ⟨_, (CFSG.pCore_normal (p := r) (G := H)).conj_mem _ (hPchar _ p hp) g.left, rfl⟩
  have hQ : IsPGroup r Q := CFSG.pCore_isPGroup.map _
  have hQrank : CFSG.Open.pRank r Q ≤ 2 := by
    rw [hQdef, pRank_map_eq_of_injective hr _ hιinj]
    exact (pRank_mono hr.one_lt le_top).trans (hrank r hr (by omega))
  obtain ⟨k, hk, φ, hφ⟩ := exists_rep hr2 Q hQ hQrank
  set φι : H →* GL (Fin k) (ZMod r) := φ.comp SemidirectProduct.inl with hφι
  set φκ : A →* GL (Fin k) (ZMod r) := φ.comp SemidirectProduct.inr with hφκ
  have hφconj : ∀ (a : A) (n : H), φι (β a n) = φκ a * φι n * (φκ a)⁻¹ := fun a n => by
    simp only [hφι, hφκ, MonoidHom.comp_apply, hconj, map_mul, map_inv]
  set T := φι.range with hTdef
  set B := φκ.range with hBdef
  have hconjT : ∀ a : A, ∀ t ∈ T, φκ a * t * (φκ a)⁻¹ ∈ T := by
    rintro a _ ⟨n, rfl⟩
    exact ⟨β a n, hφconj a n⟩
  have hBN : B ≤ normalizer (T : Set (GL (Fin k) (ZMod r))) := by
    rintro _ ⟨a, rfl⟩
    rw [mem_normalizer_iff]
    intro t
    constructor
    · exact hconjT a t
    · intro ht
      have h1 := hconjT a⁻¹ _ ht
      rw [map_inv, inv_inv] at h1
      simpa [mul_assoc] using h1
  have hTB : ⁅T, B⁆ = T := by
    refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hBN) ?_
    have hTcl : T = Subgroup.closure (φι '' {z | ∃ x : H, ∃ a : A, z = x * (β a x)⁻¹}) := by
      rw [hTdef, MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure]
    rw [hTcl, Subgroup.closure_le]
    rintro _ ⟨_, ⟨x', a, rfl⟩, rfl⟩
    have h1 : φι (x' * (β a x')⁻¹) = ⁅φι x', φκ a⁆ := by
      rw [map_mul, map_inv, hφconj, commutatorElement_def]
      group
    rw [SetLike.mem_coe, h1, ← hTcl]
    exact Subgroup.commutator_mem_commutator (MonoidHom.mem_range.mpr ⟨x', rfl⟩)
      (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
  have hT3 : ¬ 3 ∣ Nat.card T := fun h => h3 (h.trans (Subgroup.card_dvd_of_surjective
    (f := φι.rangeRestrict) φι.rangeRestrict_surjective))
  have hB3 : IsPGroup 3 B := hA.of_surjective _ φκ.rangeRestrict_surjective
  have hφy : φι y = 1 := by
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · have hT1 : T = ⊥ := by
        rw [← hTB, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro t _
        rw [mem_centralizer_iff]
        intro b _
        exact GL_comm_of_le_one (by omega) b t
      have : φι y ∈ T := ⟨y, rfl⟩
      rw [hT1, mem_bot] at this
      exact this
    · obtain rfl : k = 2 := by omega
      have hres := hgl r hr hr5 T B hT3 hB3 hBN hTB
      have hmem := rangeRestrict_mem_oResidual φι hy
      obtain ⟨n, hn⟩ := hres ⟨_, hmem⟩
      have hn' : (φι.rangeRestrict y) ^ r ^ n = 1 := by
        simpa using congrArg Subtype.val hn
      have hdvd : orderOf (φι.rangeRestrict y) ∣ orderOf y := orderOf_map_dvd _ y
      have h1 : orderOf (φι.rangeRestrict y) ∣ Nat.gcd (r ^ n) (orderOf y) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn') hdvd
      rw [(Nat.Coprime.pow_left n hcop.symm).gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
      simpa using congrArg Subtype.val h1
  have hyc := hφ (SemidirectProduct.inl y) (by rwa [orderOf_injective _ hιinj]) hφy
  have h1 := mem_centralizer_iff.mp hyc (SemidirectProduct.inl x) ⟨x, hx, rfl⟩
  apply hιinj
  rw [map_mul, map_mul]
  exact h1.symm

end ResidualFitting

end CFSG.RankThree.PartTwo.Sec16.Crit167
