module

public import CFSG.Quasithin.Vol2.Ch11SecO6B
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD.O6S

open CFSG.Open CFSG.Blueprint
open CFSG.Quasithin.Vol2.Ch11.O6
open scoped MatrixGroups

section Scalar

variable {X : Type} [Group X] [Finite X] {r : ℕ} [Fact r.Prime]

theorem actsScalar_one_of_mod {α : MulAut X} {k : ℕ} (hk : ActsScalar r α k)
    (hmod : k % r = 1) : ActsScalar r α 1 := by
  intro d hd
  have h := hk d hd
  have hw : (d ^ r) ^ (k / r) ∈ frattiniIn (CFSG.pCore r X) := pow_mem (pow_mem_frattiniIn hd) _
  have hk' : d ^ k = d * (d ^ r) ^ (k / r) := by
    rw [← pow_mul, ← pow_succ']
    congr 1
    have := Nat.div_add_mod k r
    omega
  have e : (d ^ 1)⁻¹ * α d = (d ^ r) ^ (k / r) * ((d ^ k)⁻¹ * α d) := by
    rw [hk']
    group
  rw [e]
  exact mul_mem hw h

theorem mem_frattiniIn_of_sq_mem (hr2 : r ≠ 2) {d : X} (hd : d ∈ CFSG.pCore r X)
    (h2 : d ^ 2 ∈ frattiniIn (CFSG.pCore r X)) : d ∈ frattiniIn (CFSG.pCore r X) := by
  have hr : d ^ r ∈ frattiniIn (CFSG.pCore r X) := pow_mem_frattiniIn hd
  have hcop : Nat.Coprime 2 r :=
    (Nat.coprime_primes Nat.prime_two (Fact.out : r.Prime)).mpr (Ne.symm hr2)
  have := SecG.pow_gcd_mem h2 hr
  rwa [hcop.gcd_eq_one, pow_one] at this

theorem mem_frattiniIn_of_neg_of_fix (hr2 : r ≠ 2) {α : MulAut X}
    (hα : ActsScalar r α (r - 1)) {d : X} (hd : d ∈ CFSG.pCore r X) (hfix : α d = d) :
    d ∈ frattiniIn (CFSG.pCore r X) := by
  have h := hα d hd
  rw [hfix] at h
  have hr1 : 1 ≤ r := (Fact.out : r.Prime).one_lt.le
  have hrr : d ^ r = d ^ (r - 1) * d := by rw [← pow_succ, Nat.sub_add_cancel hr1]
  apply mem_frattiniIn_of_sq_mem hr2 hd
  have hc : Commute (d ^ (r - 1)) d := Commute.pow_left (Commute.refl d) _
  have e : d ^ 2 = (d ^ (r - 1))⁻¹ * d * d ^ r := by
    rw [hrr]
    simp only [mul_assoc]
    rw [← mul_assoc d (d ^ (r - 1)) d, ← hc.eq]
    group
  rw [e]
  exact mul_mem h (pow_mem_frattiniIn hd)

theorem le_frattiniIn_of_one_of_neg (hr2 : r ≠ 2) {α : MulAut X} (h1 : ActsScalar r α 1)
    (hn : ActsScalar r α (r - 1)) {d : X} (hd : d ∈ CFSG.pCore r X) :
    d ∈ frattiniIn (CFSG.pCore r X) := by
  have hA := h1 d hd
  have hB := hn d hd
  rw [pow_one] at hA
  have hr1 : 1 ≤ r := (Fact.out : r.Prime).one_lt.le
  have hrr : d ^ r = d ^ (r - 1) * d := by rw [← pow_succ, Nat.sub_add_cancel hr1]
  apply mem_frattiniIn_of_sq_mem hr2 hd
  have hc : Commute (d ^ (r - 1)) d := Commute.pow_left (Commute.refl d) _
  have e : d ^ 2 = ((d ^ (r - 1))⁻¹ * α d) * (d⁻¹ * α d)⁻¹ * d ^ r := by
    rw [hrr]
    have e1 : ((d ^ (r - 1))⁻¹ * α d) * (d⁻¹ * α d)⁻¹ * (d ^ (r - 1) * d) =
        (d ^ (r - 1))⁻¹ * (d * d ^ (r - 1)) * d := by group
    rw [e1, ← hc.eq]
    group
  rw [e]
  exact mul_mem (mul_mem hB (inv_mem hA)) (pow_mem_frattiniIn hd)

end Scalar

section General

variable {G : Type} [Group G] [Finite G]

theorem mQuot_le_one_of {A C : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ A, a ∉ C → b ∉ C → a * b ∈ C) : E3.mQuot A (A ⊓ C) ≤ 1 := by
  have hle : (A ⊓ C).relIndex A ≤ 2 := by
    rw [Subgroup.relIndex]
    by_cases htop : (A ⊓ C).subgroupOf A = ⊤
    · rw [htop, Subgroup.index_top]
      norm_num
    · obtain ⟨⟨a₀, ha₀A⟩, ha₀⟩ : ∃ a : ↥A, a ∉ (A ⊓ C).subgroupOf A := by
        by_contra hc
        push Not at hc
        exact htop (eq_top_iff.mpr fun a _ => hc a)
      have ha₀C : a₀ ∉ C := fun h' => ha₀ (Subgroup.mem_subgroupOf.mpr ⟨ha₀A, h'⟩)
      refine (Subgroup.index_eq_two_iff.mpr ⟨⟨a₀, ha₀A⟩, fun ⟨b, hbA⟩ => ?_⟩).le
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
      by_cases hbC : b ∈ C
      · refine Or.inr ⟨⟨hbA, hbC⟩, fun ⟨_, hba⟩ => ha₀C ?_⟩
        have := C.mul_mem (C.inv_mem hbC) hba
        rwa [inv_mul_cancel_left] at this
      · exact Or.inl ⟨⟨A.mul_mem hbA ha₀A, h b hbA a₀ ha₀A hbC ha₀C⟩, fun ⟨_, hb⟩ => hbC hb⟩
  have hpos : 0 < (A ⊓ C).relIndex A := Nat.pos_of_ne_zero (E3.relIndex_ne_zero' A (A ⊓ C))
  unfold E3.mQuot
  interval_cases h' : (A ⊓ C).relIndex A <;> simp

theorem eq_self_of_inverts {X : Type} [Group X] [Finite X] {F : Subgroup X} [F.Normal]
    (hodd : Odd (Nat.card F)) (hab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) {s : X}
    (hs : ∀ f ∈ F, s * f * s⁻¹ = f⁻¹) (hsc : ∀ x : X, (s * x)⁻¹ * (x * s) ∈ F)
    {α : MulAut X} (hαF : ∀ f ∈ F, α f = f) (hαs : α s = s) (hα : ∀ x, x⁻¹ * α x ∈ F)
    (x : X) : α x = x := by
  set δ := x⁻¹ * α x with hδ
  have hδF : δ ∈ F := hα x
  set f' := (s * x)⁻¹ * (x * s) with hf'
  have hf'F : f' ∈ F := hsc x
  have hxs : x * s = s * x * f' := by rw [hf']; group
  have hαx : α x = x * δ := by rw [hδ]; group
  have h1 : α (x * s) = x * δ * s := by rw [map_mul, hαs, hαx]
  have h2 : α (s * x * f') = s * x * δ * f' := by
    rw [map_mul, map_mul, hαs, hαF f' hf'F, hαx]; group
  have hsx : s * x = x * s * f'⁻¹ := by rw [hxs]; group
  have h3 : x * δ * s = x * s * δ := by
    have := h1.symm.trans ((congrArg α hxs).trans h2)
    rw [this, hsx]
    have hc : f'⁻¹ * δ = δ * f'⁻¹ := hab _ (inv_mem hf'F) _ hδF
    calc x * s * f'⁻¹ * δ * f' = x * s * (f'⁻¹ * δ) * f' := by group
      _ = x * s * (δ * f'⁻¹) * f' := by rw [hc]
      _ = x * s * δ := by group
  have h4 : s * δ * s⁻¹ = δ := by
    have : δ * s = s * δ := by
      have := congrArg (fun y => x⁻¹ * y) h3
      simpa [mul_assoc] using this
    calc s * δ * s⁻¹ = δ * s * s⁻¹ := by rw [this]
      _ = δ := by group
  have h5 : δ = δ⁻¹ := by rw [← hs δ hδF, h4]
  have h6 : δ ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h5]
    exact mul_inv_cancel δ
  have h7 : δ ^ Nat.card F = 1 := by
    have := pow_card_eq_one' (G := ↥F) (x := ⟨δ, hδF⟩)
    have h' := congrArg Subtype.val this
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h'
  have h8 := pow_gcd_eq_one.mpr ⟨h6, h7⟩
  rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd), pow_one] at h8
  rw [hαx, h8, mul_one]

theorem eq_top_of_sup_nilpotent {X : Type} [Group X] [Finite X]
    (hperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤) {C F : Subgroup X} [C.Normal]
    (hnil : Group.IsNilpotent ↥F) (hCF : C ⊔ F = ⊤) : C = ⊤ := by
  let π := (QuotientGroup.mk' C).comp F.subtype
  have hπ : Function.Surjective π := by
    rw [← MonoidHom.range_eq_top]
    have h1 : (C ⊔ F).map (QuotientGroup.mk' C) = ⊤ := by
      rw [hCF, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective C)]
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact h1
  have hQnil : Group.IsNilpotent (X ⧸ C) := Group.nilpotent_of_surjective π hπ
  have hQperf : Group.IsPerfect (X ⧸ C) := by
    have : Group.IsPerfect X := ⟨by rw [commutator_def]; exact hperf⟩
    exact Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective C)
  by_contra hne
  have : Nontrivial (X ⧸ C) := by
    rw [QuotientGroup.nontrivial_iff]
    exact hne
  exact Group.IsPerfect.not_isSolvable (X ⧸ C) inferInstance

theorem conj_eq_inv_of_natural {X : Type} [Group X] {q : ℕ} [Fact q.Prime]
    (h2 : (2 : ZMod q) ≠ 0)
    {F : Subgroup X} [F.Normal] (hN : NaturalSL2Action q X F) {s : X} (hsF : s ∉ F)
    (hs2 : s ^ 2 ∈ F) (f : X) (hf : f ∈ F) : s * f * s⁻¹ = f⁻¹ := by
  obtain ⟨e, ψ, -, hker, hact⟩ := hN
  have hψ2 : ψ s ^ 2 = 1 := by rw [← map_pow, ← MonoidHom.mem_ker, hker]; exact hs2
  have hψ1 : ψ s ≠ 1 := fun h => hsF (hker ▸ (MonoidHom.mem_ker.mpr h))
  have hψ : ψ s = -1 :=
    (ABGLocalTools.sl2_eq_one_or_neg_one_of_sq_eq_one h2 hψ2).resolve_left hψ1
  have hm : ∀ v : Fin 2 → ZMod q,
      Matrix.mulVec ((ψ s : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) v = -v := by
    intro v
    rw [hψ]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_mulVec, Matrix.one_mulVec]
    rfl
  have h := hact s ⟨f, hf⟩
  rw [hm, ofAdd_neg, ofAdd_toAdd, ← map_inv] at h
  have h' := congrArg Subtype.val (e.injective h)
  rw [MulAut.conjNormal_apply] at h'
  exact h'

end General

section Inverts

variable {X : Type} [Group X] [Finite X]

theorem exists_prime_inverts (hD : Case1Data X)
    (hperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤) {s : X}
    (hsF : s ∉ CFSG.fittingSubgroup X)
    (hsc : ∀ x : X, x⁻¹ * (MulAut.conj s) x ∈ CFSG.fittingSubgroup X)
    (hs2 : s ^ 2 ∈ CFSG.fittingSubgroup X) {e : ℕ} (hse : s ^ 2 ^ e = 1) :
    ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card (CFSG.fittingSubgroup X) ∧
      ActsScalar r (MulAut.conj s) (r - 1) := by
  by_contra hno
  push Not at hno
  apply hsF
  apply hD.struct.1
  rw [Subgroup.mem_centralizer_iff]
  have hle : CFSG.fittingSubgroup X ≤ Subgroup.centralizer ({s} : Set X) := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun ⟨q, hq⟩ => ?_
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have : Fact q.Prime := ⟨hqp⟩
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    by_cases hqF : q ∣ Nat.card (CFSG.fittingSubgroup X)
    · have hq2 : q ≠ 2 := by
        have := hD.struct.2.1 q hqp hqF
        omega
      have hna := exists_not_triv q hD hqF (Or.inl hperf)
      have hFt : ∀ f ∈ CFSG.fittingSubgroup X,
          ActsTriviallyOnFrattiniQuotient (CFSG.pCore q X) f := fun f hf =>
        fitting_acts_triv q hf
      obtain ⟨k, hk⟩ := actsScalar_of_comm q (hD.rank q hqp hqF) hFt hna hsc
      have h2 : ActsScalar q ((MulAut.conj s) ^ 2) 1 := by
        rw [← map_pow, ← actsTrivially_iff]
        exact hFt _ hs2
      rcases actsScalar_sign q hk h2 with h1 | hm
      · have hfix := fix_of_actsScalar_one q hq2 (e := e)
          (by rw [← map_pow, hse, map_one]) h1 d hd
        rw [MulAut.conj_apply] at hfix
        calc s * d = s * d * s⁻¹ * s := by group
          _ = d * s := by rw [hfix]
      · exact absurd hm (hno q hqp hqF)
    · have h1 : d = 1 := by
        have hdF : d ∈ CFSG.fittingSubgroup X := CFSG.pCore_le_fitting X q hd
        obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp
          (CFSG.pCore_isPGroup (p := q) (G := X))
        have hdvd : Nat.card (CFSG.pCore q X) ∣ Nat.card (CFSG.fittingSubgroup X) :=
          Subgroup.card_dvd_of_le (CFSG.pCore_le_fitting X q)
        have hm0 : m = 0 := by
          by_contra hm0
          exact hqF ((dvd_pow_self q hm0).trans (hm ▸ hdvd))
        rw [hm0, pow_zero] at hm
        have := Subgroup.eq_bot_of_card_eq _ hm
        rw [this] at hd
        exact (Subgroup.mem_bot).mp hd
      rw [h1, one_mul, mul_one]
  intro f hf
  exact (Subgroup.mem_centralizer_iff.mp (hle hf) s rfl).symm

end Inverts

end CFSG.Quasithin.Vol2.Ch11.SecD.O6S
