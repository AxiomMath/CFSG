module

public import CFSG.Foundations.Basic
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms

public section

open scoped commutatorElement IsMulCommutative

namespace CFSG.RankThree.PartOne.FixedRank36

open CFSG

@[expose] def fixedSub {P : Type*} [Group P] (σ : MulAut P) : Subgroup P :=
  σ.toMonoidHom.eqLocus (MonoidHom.id P)

theorem mem_fixedSub {P : Type*} [Group P] (σ : MulAut P) (x : P) :
    x ∈ fixedSub σ ↔ σ x = x := Iff.rfl

section Rep

@[expose] noncomputable def autToEnd (q : ℕ) [Fact q.Prime] (E : Type*) [Group E]
    [IsElementaryAbelian q E] : MulAut E →* Module.End (ZMod q) (Additive E) where
  toFun σ := (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap q
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

@[expose] noncomputable def elemRep (q : ℕ) [Fact q.Prime] {L E : Type*} [Group L] [Group E]
    [IsElementaryAbelian q E] (σ : L →* MulAut E) : Representation (ZMod q) L (Additive E) :=
  (autToEnd q E).comp σ

theorem elemRep_apply (q : ℕ) [Fact q.Prime] {L E : Type*} [Group L] [Group E]
    [IsElementaryAbelian q E] (σ : L →* MulAut E) (l : L) (x : E) :
    elemRep q σ l (Additive.ofMul x) = Additive.ofMul (σ l x) := rfl

end Rep

theorem not_two_dvd_card_of_pGroup {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type*} [Group G]
    [Finite G] (hG : IsPGroup p G) : ¬ 2 ∣ Nat.card G := by
  obtain ⟨k, hk⟩ := hG.exists_card_eq
  rw [hk]
  intro h
  have h2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).mp
    (Nat.prime_two.dvd_of_dvd_pow h)
  exact hp2 h2.symm

theorem subgroup_commutator_le_center' {P : Type*} [Group P]
    (hclass : commutator P ≤ Subgroup.center P) (C : Subgroup P) :
    commutator C ≤ Subgroup.center C := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [Subgroup.mem_center_iff]
  intro z
  apply Subtype.ext
  have hxy : ⁅(x : P), (y : P)⁆ ∈ Subgroup.center P := hclass (by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hcoe : ((⁅x, y⁆ : C) : P) = ⁅(x : P), (y : P)⁆ := by
    simp [commutatorElement_def]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe]
  exact Subgroup.mem_center_iff.mp hxy z

theorem zpow_apply_eq_self_of_apply_eq_self' {X : Type*} [Group X] {σ : MulAut X} {x : X}
    (h : σ x = x) (k : ℤ) : (σ ^ k) x = x := by
  have hσ : σ ∈ MulAction.stabilizer (MulAut X) x := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact h
  have := (MulAction.stabilizer (MulAut X) x).zpow_mem hσ k
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this

section Frattini

variable {q : ℕ} [hq : Fact q.Prime] {P : Type*} [Group P] [Finite P] {L : Type*} [Group L]

@[expose] noncomputable def frattiniRep (q : ℕ) [Fact q.Prime]
    [IsElementaryAbelian q (P ⧸ frattini P)] (ρ : L →* MulAut P) :
    Representation (ZMod q) L (Additive (P ⧸ frattini P)) :=
  elemRep q ((CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini P)).comp ρ)

omit [Finite P] in
theorem frattiniRep_apply [IsElementaryAbelian q (P ⧸ frattini P)] (ρ : L →* MulAut P) (l : L)
    (x : P) :
    frattiniRep q ρ l (Additive.ofMul (x : P ⧸ frattini P)) =
      Additive.ofMul ((ρ l x : P) : P ⧸ frattini P) := by
  change Additive.ofMul
      (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini P) (ρ l)
        (QuotientGroup.mk' (frattini P) x)) = _
  rw [CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply]
  rfl

theorem frattiniRep_eq_one [IsElementaryAbelian q (P ⧸ frattini P)] (hP : IsPGroup q P)
    (hq2 : q ≠ 2) (ρ : L →* MulAut P) (l : L) (hl : IsPGroup 2 (Subgroup.zpowers (ρ l)))
    (h : frattiniRep q ρ l = 1) : ρ l = 1 := by
  have hker : ρ l ∈ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini P)).ker := by
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro x
    have h1 := congrArg (fun f : Module.End (ZMod q) (Additive (P ⧸ frattini P)) =>
      f (Additive.ofMul (x : P ⧸ frattini P))) h
    simp only [frattiniRep_apply, Module.End.one_apply] at h1
    exact congrArg Additive.toMul h1
  have hqker := CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup
    q hP
  obtain ⟨k, hk⟩ := hqker ⟨ρ l, hker⟩
  obtain ⟨m, hm⟩ := hl ⟨ρ l, Subgroup.mem_zpowers _⟩
  have hk' : (ρ l) ^ q ^ k = 1 := congrArg Subtype.val hk
  have hm' : (ρ l) ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hcop : Nat.Coprime (q ^ k) (2 ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hq.out Nat.prime_two).2 hq2)
  have := pow_gcd_eq_one.2 ⟨hk', hm'⟩
  rwa [hcop, pow_one] at this

theorem exists_fixed_lift [IsElementaryAbelian q (P ⧸ frattini P)] (hP : IsPGroup q P)
    (hq2 : q ≠ 2) (ρ : L →* MulAut P) (l : L) (hl : IsPGroup 2 (Subgroup.zpowers (ρ l)))
    (v : Additive (P ⧸ frattini P))
    (hv : v ∈ Module.End.eigenspace (frattiniRep q ρ l) 1) :
    ∃ x : P, ρ l x = x ∧ Additive.ofMul (x : P ⧸ frattini P) = v := by
  classical
  set Z := Subgroup.zpowers (ρ l) with hZ
  let α : Z →* MulAut P := Z.subtype
  have hN : ∀ b : Z, ∀ n ∈ frattini P, α b n ∈ frattini P := by
    intro b n hn
    have h := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (frattini P).Characteristic) (α b)
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hn
  have hcop : ¬ 2 ∣ Nat.card (frattini P) := not_two_dvd_card_of_pGroup hq2 (hP.to_subgroup _)
  have hset := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hl α (frattini P) hN hcop
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hvx : v = Additive.ofMul (x : P ⧸ frattini P) := by rw [hx]; rfl
  rw [Module.End.mem_eigenspace_iff, one_smul] at hv
  have hfixa : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini P) hN
      ⟨ρ l, Subgroup.mem_zpowers _⟩ (x : P ⧸ frattini P) = (x : P ⧸ frattini P) := by
    rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
    have h := hv
    rw [hvx, frattiniRep_apply] at h
    exact congrArg Additive.toMul h
  have hmem : (x : P ⧸ frattini P) ∈ {c : P ⧸ frattini P | ∀ b : Z,
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini P) hN b c = c} := by
    rintro ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hb' : (⟨ρ l ^ k, hb⟩ : Z) = ⟨ρ l, Subgroup.mem_zpowers _⟩ ^ k := Subtype.ext (by simp)
    rw [hb', map_zpow]
    exact zpow_apply_eq_self_of_apply_eq_self' hfixa k
  rw [hset] at hmem
  obtain ⟨c, hc, hcx⟩ := hmem
  refine ⟨c, hc ⟨ρ l, Subgroup.mem_zpowers _⟩, ?_⟩
  rw [hvx, ← hcx]
  rfl

theorem finrank_fixed_le [IsElementaryAbelian q (P ⧸ frattini P)] (hP : IsPGroup q P)
    (hq2 : q ≠ 2) (hexp : ∀ x : P, x ^ q = 1) (hclass : commutator P ≤ Subgroup.center P)
    (ρ : L →* MulAut P) (l : L) (hl : IsPGroup 2 (Subgroup.zpowers (ρ l)))
    (hrank : CFSG.pRank q ↥(fixedSub (ρ l)) ≤ 2) :
    Module.finrank (ZMod q) (Module.End.eigenspace (frattiniRep q ρ l) 1) ≤ 2 := by
  classical
  have hq' : q.Prime := hq.out
  set C := fixedSub (ρ l) with hC_def
  have hlift : ∀ w ∈ Module.End.eigenspace (frattiniRep q ρ l) 1,
      ∃ c ∈ C, w = Additive.ofMul (c : P ⧸ frattini P) := by
    intro w hw
    obtain ⟨x, hx, hxw⟩ := exists_fixed_lift hP hq2 ρ l hl w hw
    exact ⟨x, hx, hxw.symm⟩
  let f : C →* P ⧸ frattini P := (QuotientGroup.mk' (frattini P)).comp C.subtype
  have hcomm_ker : commutator C ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact IsMulCommutative.is_comm.comm _ _
  have hrange : Nat.card f.range ≤ Nat.card (C ⧸ commutator C) := by
    have h1 := Subgroup.card_ker_mul_card_range f
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator C)
    have h3 := Subgroup.card_le_of_le hcomm_ker
    have hpos : 0 < Nat.card f.ker := Nat.card_pos
    have h4 : Nat.card f.range * Nat.card f.ker ≤ Nat.card (C ⧸ commutator C) * Nat.card f.ker :=
      calc Nat.card f.range * Nat.card f.ker = Nat.card C := by rw [← h1, mul_comm]
        _ = Nat.card (C ⧸ commutator C) * Nat.card (commutator C) := h2
        _ ≤ Nat.card (C ⧸ commutator C) * Nat.card f.ker := Nat.mul_le_mul_left _ h3
    exact Nat.le_of_mul_le_mul_right h4 hpos
  have hCC : Nat.card (C ⧸ commutator C) ≤ q ^ 2 := by
    have hC : IsPGroup q C := hP.to_subgroup C
    have hCexp : ∀ x : C, x ^ q = 1 := fun x =>
      Subtype.ext (by rw [Subgroup.coe_pow, hexp, Subgroup.coe_one])
    have hrank' := (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hC hCexp
      (subgroup_commutator_le_center' hclass C)).1 hrank
    obtain ⟨k, hk⟩ := (hC.to_quotient (commutator C)).exists_card_eq
    have hk2 := (CFSG.RankThree.PartTwo.quotient_commutator_rank hq' hCexp hk).2
    rw [hk]
    exact Nat.pow_le_pow_right hq'.pos (hk2 ▸ hrank')
  have hcardE : Nat.card (Module.End.eigenspace (frattiniRep q ρ l) 1) ≤ q ^ 2 := by
    refine le_trans ?_ (hrange.trans hCC)
    refine Nat.card_le_card_of_injective
      (fun w => (⟨Additive.toMul (w : Additive (P ⧸ frattini P)), ?_⟩ : f.range)) ?_
    · obtain ⟨c, hc, hcw⟩ := hlift w w.2
      exact ⟨⟨c, hc⟩, by rw [hcw]; rfl⟩
    · intro w₁ w₂ h
      apply Subtype.ext
      simpa using congrArg Subtype.val h
  have : Fintype (Module.End.eigenspace (frattiniRep q ρ l) 1) := Fintype.ofFinite _
  have hpow := Module.card_eq_pow_finrank (K := ZMod q)
    (V := Module.End.eigenspace (frattiniRep q ρ l) 1)
  rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
  rw [hpow] at hcardE
  exact (Nat.pow_le_pow_iff_right hq'.one_lt).mp hcardE

end Frattini

end CFSG.RankThree.PartOne.FixedRank36
