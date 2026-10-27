module

public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSL3
public import CFSG.Quasithin.Background.A3Structure314Excl
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin.F6.InspRest

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter

section Core

variable {D : Type} [Group D] [Finite D]

theorem perfectCore_top_le_of_isSolvable (N : Subgroup D) [N.Normal]
    [Group.IsSolvable (D ⧸ N)] : perfectCore (⊤ : Subgroup D) ≤ N := by
  have h1 : perfectCore (⊤ : Subgroup (D ⧸ N)) = ⊥ :=
    (isSolvable_iff_perfectCore_eq_bot _).mp inferInstance
  have h2 := map_perfectCore (QuotientGroup.mk' N) (⊤ : Subgroup D)
  rw [Subgroup.map_top, MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective N),
    h1] at h2
  exact (QuotientGroup.ker_mk' N) ▸ (Subgroup.map_eq_bot_iff _).mp h2

theorem perfectCore_top_eq_of_isSolvable (N : Subgroup D) [N.Normal] [Group.IsSolvable (D ⧸ N)]
    (hN : ⁅N, N⁆ = N) : perfectCore (⊤ : Subgroup D) = N :=
  le_antisymm (perfectCore_top_le_of_isSolvable N) (le_perfectCore_of_perfect le_top hN)

omit [Finite D] in
theorem isSolvable_quotient_of_sq_mem (N : Subgroup D) [N.Normal] (hsq : ∀ x : D, x ^ 2 ∈ N) :
    Group.IsSolvable (D ⧸ N) := by
  have hinv : ∀ q : D ⧸ N, q⁻¹ = q := by
    intro q
    refine inv_eq_of_mul_eq_one_right ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← sq]
      exact hsq x
  refine Group.isSolvable_of_comm fun a b => ?_
  calc a * b = (a * b)⁻¹ := (hinv _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv, hinv]

omit [Finite D] in
theorem commutator_eq_self_of_isQuasisimple {N : Subgroup D} (hq : CFSG.IsQuasisimple ↥N) :
    ⁅N, N⁆ = N :=
  Subgroup.isPerfect_iff.mp hq.1

end Core

section Iso

@[expose] noncomputable def centralQuotientCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.IsQuasisimple B) : CFSG.IsQuasisimple A := by
  obtain ⟨hperf, hs, a, b, hab⟩ := h
  let f := centralQuotientCongr e
  refine ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective,
    f.isSimpleGroup, f.symm a, f.symm b, fun hc => hab ?_⟩
  simpa using congrArg f hc

@[expose] noncomputable def quotientCenterEquivOfSimple {N : Type*} [Group N] [IsSimpleGroup N]
    (hnc : ∃ a b : N, a * b ≠ b * a) : N ⧸ Subgroup.center N ≃* N :=
  (QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).2).trans QuotientGroup.quotientBot

end Iso

section Witness

@[expose] def SqWitness (D : Type) [Group D] (P : ∀ (W : Type) [Group W], Prop) : Prop :=
  ∃ N : Subgroup D, N.Normal ∧ (∀ x : D, x ^ 2 ∈ N) ∧ CFSG.IsQuasisimple ↥N ∧
    P (↥N ⧸ Subgroup.center ↥N)

variable {P : ∀ (W : Type) [Group W], Prop}

theorem SqWitness.of_mulEquiv (hP : ∀ {A B : Type} [Group A] [Group B], (A ≃* B) → P B → P A)
    {D D' : Type} [Group D] [Group D'] (e : D ≃* D') (h : SqWitness D' P) : SqWitness D P := by
  obtain ⟨N, hN, hsq, hq, hPN⟩ := h
  let f : ↥(N.map e.symm.toMonoidHom) ≃* ↥N :=
    (N.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm
  refine ⟨N.map e.symm.toMonoidHom, hN.map _ e.symm.surjective, fun x => ?_,
    isQuasisimple_of_mulEquiv f hq, hP (centralQuotientCongr f) hPN⟩
  exact Subgroup.mem_map.2 ⟨e x ^ 2, hsq (e x), by simp⟩

theorem sqWitness_top {D : Type} [Group D]
    (hP : ∀ {A B : Type} [Group A] [Group B], (A ≃* B) → P B → P A) (hq : CFSG.IsQuasisimple D)
    (hPD : P (D ⧸ Subgroup.center D)) : SqWitness D P :=
  ⟨⊤, inferInstance, fun _ => trivial, isQuasisimple_of_mulEquiv Subgroup.topEquiv hq,
    hP (centralQuotientCongr Subgroup.topEquiv) hPD⟩

theorem sqWitness_top_of_simple {D : Type} [Group D] [IsSimpleGroup D]
    (hP : ∀ {A B : Type} [Group A] [Group B], (A ≃* B) → P B → P A)
    (hnc : ∃ a b : D, a * b ≠ b * a) (hPD : P D) : SqWitness D P :=
  sqWitness_top hP (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
    (hP (quotientCenterEquivOfSimple hnc) hPD)

theorem sqWitness_of_index_two {D : Type} [Group D] {N : Subgroup D} [N.Normal]
    (hidx : N.index = 2) (hq : CFSG.IsQuasisimple ↥N) (hPN : P (↥N ⧸ Subgroup.center ↥N)) :
    SqWitness D P := by
  have : N.FiniteIndex := ⟨by omega⟩
  refine ⟨N, inferInstance, fun x => ?_, hq, hPN⟩
  have := Subgroup.pow_index_mem N x
  rwa [hidx] at this

theorem spec_of_sqWitness (hP : ∀ {A B : Type} [Group A] [Group B], (A ≃* B) → P B → P A)
    {D : Type} [Group D] [Finite D] (h : SqWitness D P) :
    CFSG.IsQuasisimple ↥(perfectCore (⊤ : Subgroup D)) ∧
      P (↥(perfectCore (⊤ : Subgroup D)) ⧸ Subgroup.center ↥(perfectCore (⊤ : Subgroup D))) := by
  obtain ⟨N, hN, hsq, hq, hPN⟩ := h
  have : Group.IsSolvable (D ⧸ N) := isSolvable_quotient_of_sq_mem N hsq
  have hcore := perfectCore_top_eq_of_isSolvable N (commutator_eq_self_of_isQuasisimple hq)
  let e : ↥(perfectCore (⊤ : Subgroup D)) ≃* ↥N := MulEquiv.subgroupCongr hcore
  exact ⟨isQuasisimple_of_mulEquiv e hq, hP (centralQuotientCongr e) hPN⟩

end Witness

section L2

theorem exists_noncomm_of_isL2 {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hq : 5 ≤ p ^ e) {W : Type} [Group W] (h : IsL2 p e W) : ∃ a b : W, a * b ≠ b * a := by
  have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity W 2 p e h).2
  obtain ⟨-, K, _, _, hK, ⟨f⟩⟩ := h
  let g : W ≃* CFSG.GorensteinWalter.PSL2 K :=
    f.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have : Finite W := Finite.of_equiv _ g.symm.toEquiv
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, e, hp, hp.odd_of_ne_two hp2, he, hK⟩
  have hcard : Nat.card W = p ^ e * ((p ^ e) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr g.toEquiv, CFSG.GorensteinWalter.psl2_card_formula K hodd, hK]
  refine CFSG.Quasithin.A314.exists_noncomm_of_simple hs ?_
  rw [hcard]
  have hq2 : 2 ∣ (p ^ e) ^ 2 - 1 := by
    have hodd' : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
    obtain ⟨k, hk⟩ := hodd'
    exact ⟨2 * k * k + 2 * k, by rw [hk]; ring_nf; omega⟩
  obtain ⟨m, hm⟩ := hq2
  have hm2 : 2 ≤ m := by
    have : 25 ≤ (p ^ e) ^ 2 := by nlinarith
    omega
  have hdiv : p ^ e * ((p ^ e) ^ 2 - 1) / 2 = p ^ e * m := by
    rw [hm, show p ^ e * (2 * m) = 2 * (p ^ e * m) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [hdiv]
  exact Nat.not_prime_mul (by omega) (by omega)

end L2

section SL3

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem center_eq_statedScalars (H : Subgroup (GL ι K)) (hq : CFSG.IsQuasisimple ↥H)
    (hs : IsSimpleGroup (StatedProj H)) :
    Subgroup.center ↥H = (CFSG.Assembly.LowTwoRank.StatedScalars ι K).subgroupOf H := by
  set C := (CFSG.Assembly.LowTwoRank.StatedScalars ι K).subgroupOf H with hC
  have hCZ : C ≤ Subgroup.center ↥H := Gold14610.Struct.statedScalars_subgroupOf_le_center H
  refine le_antisymm ?_ hCZ
  set π := QuotientGroup.mk' C with hπ
  have hn : ((Subgroup.center ↥H).map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective C)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.center ↥H).map π) with hbot | htop
  · intro z hz
    have h1 : π z ∈ (Subgroup.center ↥H).map π := ⟨z, hz, rfl⟩
    rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hq
    have hZ : Subgroup.center ↥H = ⊤ := by
      rw [eq_top_iff]
      intro h _
      have h1 : π h ∈ (Subgroup.center ↥H).map π := by rw [htop]; trivial
      obtain ⟨z, hz, hzh⟩ := h1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hzh
      have h2 := Subgroup.mul_mem _ hz (hCZ hzh)
      simpa using h2
    apply hab
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        rw [hZ]
        trivial

@[expose] noncomputable def quotientCenterEquivStatedProj (H : Subgroup (GL ι K))
    (hq : CFSG.IsQuasisimple ↥H) (hs : IsSimpleGroup (StatedProj H)) :
    ↥H ⧸ Subgroup.center ↥H ≃* StatedProj H :=
  QuotientGroup.quotientMulEquivOfEq (center_eq_statedScalars H hq hs)

theorem exists_noncomm_statedProj (H : Subgroup (GL ι K)) (hq : CFSG.IsQuasisimple ↥H)
    (hs : IsSimpleGroup (StatedProj H)) : ∃ a b : StatedProj H, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hq.2.2
  let f := quotientCenterEquivStatedProj H hq hs
  exact ⟨f a, f b, fun hc => hab (by simpa using congrArg f.symm hc)⟩

theorem isQuasisimple_and_quotientCenter (H : Subgroup (GL ι K)) (hq : CFSG.IsQuasisimple ↥H)
    (hs : IsSimpleGroup (StatedProj H)) {W : Type} [Group W]
    (hW : Nonempty (W ≃* ↥H) ∨ Nonempty (W ≃* StatedProj H)) :
    CFSG.IsQuasisimple W ∧ Nonempty (W ⧸ Subgroup.center W ≃* StatedProj H) := by
  rcases hW with hf | hf
  · obtain ⟨f⟩ := hf
    exact ⟨isQuasisimple_of_mulEquiv f hq,
      ⟨(centralQuotientCongr f).trans (quotientCenterEquivStatedProj H hq hs)⟩⟩
  · obtain ⟨f⟩ := hf
    have hnc := exists_noncomm_statedProj H hq hs
    have : IsSimpleGroup W := f.isSimpleGroup
    have hncW : ∃ a b : W, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnc
      exact ⟨f.symm a, f.symm b, fun hc => hab (by simpa using congrArg f hc)⟩
    exact ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hncW).1,
      ⟨(quotientCenterEquivOfSimple hncW).trans f⟩⟩

theorem isQuasisimple_and_isSLEps3 {p : ℕ} (hp3 : 3 ≤ p) {W : Type} [Group W]
    (h : IsSLEps3 p W) : CFSG.IsQuasisimple W ∧ IsSLEps3 p (W ⧸ Subgroup.center W) := by
  obtain ⟨hp, K, _, _, hK⟩ := h
  rcases hK with ⟨h1, h2, hW⟩ | ⟨h1, h2, hW⟩
  · obtain ⟨hqW, ⟨f⟩⟩ := isQuasisimple_and_quotientCenter (StatedSL 3 K)
      (Gold14610.Struct.isQuasisimple_statedSL_three hp K h2)
      (Gold14610.Struct.isSimpleGroup_statedProj_statedSL_three hp K h2) hW
    exact ⟨hqW, hp, K, inferInstance, inferInstance, Or.inl ⟨h1, h2, Or.inr ⟨f⟩⟩⟩
  · obtain ⟨hqW, ⟨f⟩⟩ := isQuasisimple_and_quotientCenter (StatedSU 3 p K)
      (Gold14610.Struct.isQuasisimple_statedSU_three hp hp3 K h2)
      (Gold14610.Struct.isSimpleGroup_statedProj_statedSU_three hp hp3 K h2) hW
    exact ⟨hqW, hp, K, inferInstance, inferInstance, Or.inr ⟨h1, h2, Or.inr ⟨f⟩⟩⟩

end SL3

end CFSG.Quasithin.F6.InspRest
