module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb
public import CFSG.RankThree.PartOne.CTP.SeitzL2
public import CFSG.RankThree.PartTwo.Sec21.Item22L2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open

namespace P2251L

theorem exists_orderOf_three_fixed_psl2FieldAut (F : Type) [Field F] [CharP F 2] :
    ∃ c : CFSG.GorensteinWalter.PSL2 F, orderOf c = 3 ∧
      ∀ τ : F ≃+* F, CFSG.GorensteinWalter.psl2FieldAut F τ c = c := by
  have hinj : Function.Injective
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (CFSG.RankThree.PartTwo.Sec21.eq_one_of_mem_center_sl2 hx)
  refine ⟨QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
    CFSG.RankThree.PartTwo.Sec21.sl2OrderThree, ?_, fun τ => ?_⟩
  · rw [orderOf_injective _ hinj, CFSG.RankThree.PartTwo.Sec21.orderOf_sl2OrderThree]
  · rw [CFSG.GorensteinWalter.psl2FieldAut_apply, CFSG.GorensteinWalter.psl2RingEquiv_mk]
    congr 1
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.map_apply_coe, CFSG.RankThree.PartTwo.Sec21.coe_sl2OrderThree]

theorem exists_fixed_orderOf_three_psl2 {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {σ : MulAut (CFSG.GorensteinWalter.PSL2 F)} (hσ : orderOf σ = p)
    (hσi : ∀ g, σ ≠ MulAut.conj g) : ∃ c : CFSG.GorensteinWalter.PSL2 F, orderOf c = 3 ∧ σ c = c := by
  obtain ⟨τ, β, -, hτ⟩ :=
    CFSG.RankThree.PartOne.CTP.exists_conj_fieldAut hp (hp.odd_of_ne_two hp2) ⟨hσ, hσi⟩
  obtain ⟨c, hc, hfc⟩ := exists_orderOf_three_fixed_psl2FieldAut F
  refine ⟨β c, by rw [MulEquiv.orderOf_eq, hc], ?_⟩
  rw [hτ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hfc]

theorem exists_fixed_orderOf_three {X : Type} [Group X] {n : ℕ} (h : IsL2Ev X n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (z : MulAut X) (hz : orderOf z = p) (hzi : z ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ x : X, orderOf x = 3 ∧ z x = x := by
  obtain ⟨F, _, _, _, -, ⟨e⟩⟩ := P22y.exists_equiv_psl2 h
  have hz'i : ∀ g, MulAut.congr e z ≠ MulAut.conj g := by
    intro g hg
    apply hzi
    refine ⟨e.symm g, MulEquiv.ext fun x => ?_⟩
    have h1 : e (z x) = g * e x * g⁻¹ := by
      have := congrArg (fun α : MulAut (CFSG.GorensteinWalter.PSL2 F) => α (e x)) hg
      simpa [MulAut.congr_apply, MulAut.conj_apply] using this
    rw [MulAut.conj_apply]
    apply e.injective
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply, h1]
  obtain ⟨c, hc, hzc⟩ :=
    exists_fixed_orderOf_three_psl2 hp hp2 (by rw [MulEquiv.orderOf_eq, hz]) hz'i
  refine ⟨e.symm c, by rw [MulEquiv.orderOf_eq, hc], ?_⟩
  apply e.injective
  rw [e.apply_symm_apply]
  exact hzc

theorem isCyclic_range_inf_inner_of {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) {p : ℕ}
    (hcp : ∀ B : Subgroup X, IsPGroup p B → IsCyclic B) {P : Type} [Group P] (hexp : ∀ x : P, x ^ p = 1)
    (φ : P →* MulAut X) : IsCyclic ↥(φ.range ⊓ (MulAut.conj : X →* MulAut X).range) := by
  have hinj := P22y.conj_injective_of_center_eq_bot hZ
  set B : Subgroup X := (φ.range ⊓ (MulAut.conj : X →* MulAut X).range).comap MulAut.conj
  have hBp : IsPGroup p B := by
    intro b
    refine ⟨1, ?_⟩
    obtain ⟨y, hy⟩ := b.2.1
    have h1 : MulAut.conj ((b : X) ^ p) = 1 := by
      rw [map_pow, ← hy, ← map_pow, hexp, map_one]
    rw [pow_one]
    exact Subtype.ext (hinj (h1.trans (map_one _).symm))
  haveI := hcp B hBp
  have hmap : B.map (MulAut.conj : X →* MulAut X) = φ.range ⊓ (MulAut.conj : X →* MulAut X).range :=
    Subgroup.map_comap_eq_self inf_le_right
  rw [← hmap]
  exact isCyclic_of_surjective ((MulAut.conj : X →* MulAut X).subgroupMap B)
    ((MulAut.conj : X →* MulAut X).subgroupMap_surjective B)

theorem exists_orderOf_three_index_le_of {X : Type} [Group X] [Finite X] {P : Type} [Group P] [Finite P] {p : ℕ}
    (hp : p.Prime) (hexp : ∀ x : P, x ^ p = 1) (hPab : ∀ x y : P, x * y = y * x) (φ : P →* MulAut X)
    (h3 : ∃ x : X, orderOf x = 3) (hcyc : IsCyclic ↥(φ.range ⊓ (MulAut.conj : X →* MulAut X).range))
    (hquot : ∀ x ∈ φ.range, ∀ y ∈ φ.range, x ∉ (MulAut.conj : X →* MulAut X).range →
      ∃ k : ℕ, x ^ k * y ∈ (MulAut.conj : X →* MulAut X).range)
    (hfix : ∀ z ∈ φ.range, z ∉ (MulAut.conj : X →* MulAut X).range → ∃ x : X, orderOf x = 3 ∧ z x = x) :
    ∃ x : X, orderOf x = 3 ∧ ∃ Q : Subgroup P, Q.index ≤ p ∧ ∀ u ∈ Q, φ u x = x := by
  letI : MulAction (MulAut X) {x : X // orderOf x = 3} :=
    { smul := fun f x => ⟨f x.1, (MulEquiv.orderOf_eq f x.1).trans x.2⟩
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }
  obtain ⟨x₀, hx₀⟩ := h3
  haveI : Nonempty {x : X // orderOf x = 3} := ⟨⟨x₀, hx₀⟩⟩
  obtain ⟨ω, hω⟩ := uc22p22y_exists_fixed_index_le (Ω := {x : X // orderOf x = 3}) hp hexp hPab φ
    (MulAut.conj : X →* MulAut X).range hcyc hquot fun z hz hzi => by
      obtain ⟨x, hx, hzx⟩ := hfix z hz hzi
      exact ⟨⟨x, hx⟩, Subtype.ext hzx⟩
  refine ⟨ω.1, ω.2, (MulAction.stabilizer (MulAut X) ω).comap φ, hω, fun u hu => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_comap.1 hu))

theorem exists_orderOf_three_index_le {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2Ev X n) {P : Type}
    [Group P] [Finite P] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ x : P, x ^ p = 1)
    (hPab : ∀ x y : P, x * y = y * x) (φ : P →* MulAut X) :
    ∃ x : X, orderOf x = 3 ∧ ∃ Q : Subgroup P, Q.index ≤ p ∧ ∀ u ∈ Q, φ u x = x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hrp : ∀ x ∈ φ.range, x ^ p = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow, hexp, map_one]
  have h3 : ∃ x : X, orderOf x = 3 := by
    obtain ⟨F, _, _, _, -, ⟨e⟩⟩ := P22y.exists_equiv_psl2 h
    obtain ⟨c, hc, -⟩ := exists_orderOf_three_fixed_psl2FieldAut F
    exact ⟨e.symm c, by rw [MulEquiv.orderOf_eq, hc]⟩
  refine exists_orderOf_three_index_le_of hp hexp hPab φ h3 (P22y.isCyclic_range_inf_inner h hp hp2 hexp φ)
    (fun x hx y hy hxi => P22y.exists_pow_mul_mem_inner h hp (hrp x hx) (hrp y hy) hxi) fun z hz hzi => ?_
  have hz1 : z ≠ 1 := fun h1 => hzi (h1 ▸ Subgroup.one_mem _)
  exact exists_fixed_orderOf_three h hp hp2 z (orderOf_eq_prime (hrp z hz) hz1) hzi

theorem exists_orderOf_three_index_le_of_le_inner {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    {p : ℕ} (hp : p.Prime) (hcp : ∀ B : Subgroup X, IsPGroup p B → IsCyclic B) (h3 : ∃ x : X, orderOf x = 3)
    {P : Type} [Group P] [Finite P] (hexp : ∀ x : P, x ^ p = 1) (hPab : ∀ x y : P, x * y = y * x)
    (φ : P →* MulAut X) (hinn : φ.range ≤ (MulAut.conj : X →* MulAut X).range) :
    ∃ x : X, orderOf x = 3 ∧ ∃ Q : Subgroup P, Q.index ≤ p ∧ ∀ u ∈ Q, φ u x = x :=
  exists_orderOf_three_index_le_of hp hexp hPab φ h3 (isCyclic_range_inf_inner_of hZ hcp hexp φ)
    (fun _ hx _ _ hxi => absurd (hinn hx) hxi) fun _ hz hzi => absurd (hinn hz) hzi

theorem pow_le_card_of_index_le {P : Type} [Group P] {p k : ℕ} (hp : 0 < p) {Q : Subgroup P}
    (hQ : Q.index ≤ p) (hP : p ^ (k + 1) ≤ Nat.card P) : p ^ k ≤ Nat.card Q := by
  refine Nat.le_of_mul_le_mul_right ?_ hp
  calc p ^ k * p = p ^ (k + 1) := (pow_succ p k).symm
    _ ≤ Nat.card P := hP
    _ = Nat.card Q * Q.index := Q.card_mul_index.symm
    _ ≤ Nat.card Q * p := Nat.mul_le_mul_left _ hQ

theorem exists_orderOf_three_card_le {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2Ev X n) {P : Type}
    [Group P] [Finite P] {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ x : P, x ^ p = 1)
    (hPab : ∀ x y : P, x * y = y * x) (φ : P →* MulAut X) (hP : p ^ (k + 1) ≤ Nat.card P) :
    ∃ x : X, orderOf x = 3 ∧ ∃ Q : Subgroup P, p ^ k ≤ Nat.card Q ∧ ∀ u ∈ Q, φ u x = x := by
  obtain ⟨x, hx, Q, hQ, hQx⟩ := exists_orderOf_three_index_le h hp hp2 hexp hPab φ
  exact ⟨x, hx, Q, pow_le_card_of_index_le hp.pos hQ hP, hQx⟩

end P2251L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
