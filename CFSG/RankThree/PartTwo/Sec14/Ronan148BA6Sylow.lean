module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

variable {H : Type} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]

theorem inf_eq_bot_of_isPGroup {N P : Subgroup H} (hN : ¬ p ∣ Nat.card N) (hP : IsPGroup p P) :
    N ⊓ P = ⊥ := by
  refine Subgroup.eq_bot_of_card_eq _ ?_
  have h1 : Nat.card ↥(N ⊓ P) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk⟩ := (hP.to_le (inf_le_right : N ⊓ P ≤ P)).exists_card_eq
  rcases k with _ | k
  · simpa using hk
  · exfalso
    apply hN
    rw [hk] at h1
    exact (dvd_pow_self p (Nat.succ_ne_zero k)).trans h1

theorem card_map_mk'_of_isPGroup {N : Subgroup H} [N.Normal] (hN : ¬ p ∣ Nat.card N)
    {P : Subgroup H} (hP : IsPGroup p P) :
    Nat.card (P.map (QuotientGroup.mk' N)) = Nat.card P := by
  have hdisj := inf_eq_bot_of_isPGroup hN hP
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp P.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hx' : (x : H) ∈ N ⊓ P := ⟨hx, x.2⟩
    rw [hdisj, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (Subtype.ext hx')
  rw [← Subgroup.range_subtype P, ← MonoidHom.range_comp, Subgroup.range_subtype]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem exists_le_map_eq_of_le_map {N : Subgroup H} [N.Normal] (hN : ¬ p ∣ Nat.card N)
    {U : Subgroup H} {E : Subgroup (H ⧸ N)} (hEU : E ≤ U.map (QuotientGroup.mk' N))
    (hE : IsPGroup p E) :
    ∃ P : Subgroup H, P ≤ U ∧ IsPGroup p P ∧ P.map (QuotientGroup.mk' N) = E ∧
      Nat.card P = Nat.card E := by
  set V := U ⊓ E.comap (QuotientGroup.mk' N) with hV
  let f : ↥V →* ↥E :=
    { toFun := fun v => ⟨QuotientGroup.mk' N v, v.2.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun v w => Subtype.ext (map_mul _ _ _) }
  have hf : Function.Surjective f := by
    rintro ⟨e, he⟩
    obtain ⟨u, hu, rfl⟩ := hEU he
    exact ⟨⟨u, hu, he⟩, rfl⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p ↥V))
  set S' := S.mapSurjective hf with hS'
  have : Finite ↥E := inferInstance
  have hS'top : (S' : Subgroup ↥E) = ⊤ := by
    obtain ⟨k, hk⟩ := hE.exists_card_eq
    have h1 := S'.card_eq_multiplicity
    rw [hk, Nat.Prime.factorization_pow hp.out, Finsupp.single_eq_same] at h1
    rw [← Subgroup.card_eq_iff_eq_top, h1, hk]
  set P := (S : Subgroup ↥V).map V.subtype with hPdef
  have hPU : P ≤ U := (Subgroup.map_subtype_le _).trans inf_le_left
  have hPp : IsPGroup p P := S.2.map V.subtype
  have hPE : P.map (QuotientGroup.mk' N) = E := by
    have h1 : P.map (QuotientGroup.mk' N) = ((S : Subgroup ↥V).map f).map E.subtype := by
      rw [hPdef, Subgroup.map_map, Subgroup.map_map]
      rfl
    have h2 : (S : Subgroup ↥V).map f = ⊤ := by
      rw [← hS'top, hS', Sylow.coe_mapSurjective]
    rw [h1, h2, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨P, hPU, hPp, hPE, ?_⟩
  rw [← hPE, card_map_mk'_of_isPGroup hN hPp]

theorem exists_mem_map_conj_eq_of_map_eq {N : Subgroup H} [N.Normal] (hN : ¬ p ∣ Nat.card N)
    {P₁ P₂ : Subgroup H} (hP₁ : IsPGroup p P₁) (hcard : Nat.card P₂ = Nat.card P₁)
    (h : P₁.map (QuotientGroup.mk' N) = P₂.map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, P₂ = P₁.map (MulAut.conj n).toMonoidHom := by
  have hle : P₂ ≤ P₁ ⊔ N := by
    intro y hy
    have hy' : QuotientGroup.mk' N y ∈ P₁.map (QuotientGroup.mk' N) := by
      rw [h]
      exact ⟨y, hy, rfl⟩
    obtain ⟨q, hq, hqy⟩ := hy'
    have hn : q⁻¹ * y ∈ N := by
      rw [← QuotientGroup.eq]
      exact hqy
    have : y = q * (q⁻¹ * y) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hn)
  set M := P₁ ⊔ N with hMdef
  have hdisj : N ⊓ P₁ = ⊥ := inf_eq_bot_of_isPGroup hN hP₁
  have hM : Nat.card M = Nat.card P₁ * Nat.card N := by
    have h1 := Subgroup.relIndex_mul_card N M
    have h2 : N.relIndex M = N.relIndex P₁ := Subgroup.relIndex_sup_right P₁ N
    have h3 := Subgroup.relIndex_mul_card N P₁
    rw [hdisj, Subgroup.card_bot, mul_one] at h3
    rw [inf_of_le_left le_sup_right, h2, h3] at h1
    exact h1.symm
  obtain ⟨k, hk⟩ := hP₁.exists_card_eq
  have hfac : (Nat.card M).factorization p = k := by
    rw [hM, hk, Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) Nat.card_pos.ne',
      Nat.Prime.factorization_pow hp.out, Finsupp.add_apply, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hN, add_zero]
  have hQM : Nat.card (P₁.subgroupOf M) = p ^ (Nat.card M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, hk, hfac]
  have hP'M : Nat.card (P₂.subgroupOf M) = p ^ (Nat.card M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard, hk, hfac]
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (↥M) (Sylow.ofCard _ hQM) (Sylow.ofCard _ hP'M)
  have hm' : P₂.subgroupOf M = (P₁.subgroupOf M).map (MulAut.conj m).toMonoidHom := by
    have := congrArg (fun S : Sylow p M => (S : Subgroup M)) hm
    simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at this
    rw [← this, Subgroup.pointwise_smul_def]
    rfl
  have hP₂m : P₂ = P₁.map (MulAut.conj (m : H)).toMonoidHom := by
    have hP₂eq : P₂ = (P₂.subgroupOf M).map M.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hle]
    rw [hP₂eq, hm', Subgroup.map_map]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
    · rintro ⟨y, hy, rfl⟩
      have hyM : y ∈ M := Subgroup.mem_sup_left hy
      exact ⟨⟨y, hyM⟩, hy, by simp [MulAut.conj_apply]⟩
  have hmM : (m : H) ∈ ((P₁ ⊔ N : Subgroup H) : Set H) := m.2
  rw [Subgroup.mul_normal P₁ N] at hmM
  obtain ⟨q, hq, n₀, hn₀, hqn⟩ := Set.mem_mul.mp hmM
  refine ⟨q * n₀ * q⁻¹, (inferInstance : N.Normal).conj_mem n₀ hn₀ q, ?_⟩
  rw [hP₂m]
  have hmq : (m : H) = q * n₀ * q⁻¹ * q := by rw [← hqn]; group
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨q * y * q⁻¹, P₁.mul_mem (P₁.mul_mem hq hy) (P₁.inv_mem hq), ?_⟩
    simp only [MonoidHom.coe_coe, MulAut.conj_apply, MulEquiv.coe_toMonoidHom, hmq]
    group
  · rintro ⟨y, hy, rfl⟩
    refine ⟨q⁻¹ * y * q, P₁.mul_mem (P₁.mul_mem (P₁.inv_mem hq) hy) hq, ?_⟩
    simp only [MonoidHom.coe_coe, MulAut.conj_apply, MulEquiv.coe_toMonoidHom, hmq]
    group

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
