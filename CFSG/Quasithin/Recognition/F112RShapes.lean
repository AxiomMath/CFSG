module

public import CFSG.Quasithin.EmptyFaithful.S1422Extra
public import CFSG.Quasithin.Background.F6SQTK

public section

namespace CFSG.Quasithin

open CFSG.Open

theorem isCommutingGeneration_map {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    {A B : Subgroup P} (h : IsCommutingGeneration A B) :
    IsCommutingGeneration (A.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  obtain ⟨hAB, hgen⟩ := h
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (hAB ha) b hb
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    exact congrArg e this
  · rw [← Subgroup.map_sup, hgen, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.surjective

theorem IsZ4Sq.of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) (h : IsZ4Sq P) :
    IsZ4Sq Q := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem IsZ4StarQ8.of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) (h : IsZ4StarQ8 P) :
    IsZ4StarQ8 Q := by
  obtain ⟨hcard, A, B, hAB, hA4, hAc, ⟨eB⟩⟩ := h
  refine ⟨by rw [← Nat.card_congr e.toEquiv, hcard], A.map e.toMonoidHom, B.map e.toMonoidHom,
    isCommutingGeneration_map e hAB, ?_, ?_, ⟨(e.subgroupMap B).symm.trans eB⟩⟩
  · exact (Nat.card_congr (e.subgroupMap A).toEquiv).symm.trans hA4
  · exact ((e.subgroupMap A).isCyclic).mp hAc

private theorem map_center_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) :
    (Subgroup.center P).map e.toMonoidHom = Subgroup.center Q := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' := Subgroup.mem_center_iff.mp ha
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    have := ha' (e.symm g)
    have h2 := congrArg e this
    simpa using h2
  · intro hx
    have hx' := Subgroup.mem_center_iff.mp hx
    refine ⟨e.symm x, Subgroup.mem_center_iff.mpr fun g => ?_, by simp⟩
    have := hx' (e g)
    have h2 := congrArg e.symm this
    simpa using h2

private theorem map_frattini_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) :
    (frattini P).map e.toMonoidHom = frattini Q := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom) e.surjective
  · intro x hx
    have h1 : frattini Q ≤ (frattini P).comap e.symm.toMonoidHom :=
      frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective
    exact ⟨e.symm x, h1 hx, by simp⟩

private theorem map_commutator_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) :
    (commutator P).map e.toMonoidHom = commutator Q := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  rfl

theorem IsSpecialPow.of_mulEquiv {p q w : ℕ} {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (h : IsSpecialPow p q w P) : IsSpecialPow p q w Q := by
  obtain ⟨⟨hp, hs⟩, hcard, hcen⟩ := h
  have hcenQ : Nat.card (Subgroup.center Q) = q := by
    rw [← map_center_mulEquiv e, ← hcen]
    exact (Nat.card_congr (e.subgroupMap (Subgroup.center P)).toEquiv).symm
  refine ⟨⟨hp.of_equiv e, ?_⟩, by rw [← Nat.card_congr e.toEquiv, hcard], hcenQ⟩
  rcases hs with ⟨hcomm, hexp⟩ | ⟨hc, hf, hz⟩
  · refine Or.inl ⟨⟨⟨fun a b => ?_⟩⟩, fun x => ?_⟩
    · have := hcomm.is_comm.comm (e.symm a) (e.symm b)
      have h2 := congrArg e this
      simpa using h2
    · have := hexp (e.symm x)
      have h2 := congrArg e this
      simpa [← map_pow] using h2
  · refine Or.inr ⟨?_, ?_, fun z hz' => ?_⟩
    · rw [← map_commutator_mulEquiv e, hc, map_center_mulEquiv e]
    · rw [← map_frattini_mulEquiv e, hf, map_center_mulEquiv e]
    · rw [← map_center_mulEquiv e] at hz'
      obtain ⟨a, ha, rfl⟩ := hz'
      have := hz a ha
      have h2 := congrArg e this
      simpa [← map_pow] using h2

private theorem le_centralizer_of_commute {R : Type*} [Group R] {X Y : Subgroup R}
    (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) : X ≤ Subgroup.centralizer (Y : Set R) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (h x hx y hy).symm

theorem isSpecialPow_of_isSpecialTwoOnePlusFour {R : Type*} [Group R]
    (h : F6.IsSpecialTwoOnePlusFour R) : IsSpecialPow 2 2 2 R := by
  obtain ⟨hcard, hZ, hc, hf⟩ := h
  have hfin : Finite R := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 R := IsPGroup.of_card hcard
  refine ⟨⟨hp, Or.inr ⟨hc, hf, fun z hz => ?_⟩⟩, by simpa using hcard, hZ⟩
  have h2 : (⟨z, hz⟩ : Subgroup.center R) ^ 2 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center R) (x := ⟨z, hz⟩)
    rw [hZ] at this
    exact this
  exact congrArg Subtype.val h2

theorem isZ4StarQ8_of_centralProduct₂ {R : Type*} [Group R] [Finite R]
    (h : F6.IsCentralProduct₂ R (Multiplicative (ZMod 4)) (QuaternionGroup 2)) :
    IsZ4StarQ8 R := by
  obtain ⟨A, B, hgen, hcomm, ⟨eA⟩, ⟨eB⟩, hAB2⟩ := h
  have hAB := le_centralizer_of_commute hcomm
  have hA4 : Nat.card A = 4 := by
    rw [Nat.card_congr eA.toEquiv]
    simp
  have hB8 : Nat.card B = 8 := by rw [Nat.card_congr eB.toEquiv, card_quaternion_two]
  have hprod := card_sup_mul_card_inf_of_le_centralizer hAB
  rw [hgen, Subgroup.card_top, hAB2, hA4, hB8] at hprod
  refine ⟨by omega, A, B, ⟨hAB, hgen⟩, hA4, ?_, ⟨eB⟩⟩
  exact (eA.isCyclic).mpr inferInstance

theorem isQ8Sq_of_centralProduct₂ {R : Type*} [Group R] [Finite R]
    (h : F6.IsCentralProduct₂ R (QuaternionGroup 2) (QuaternionGroup 2)) : IsQ8Sq R := by
  obtain ⟨A, B, hgen, hcomm, ⟨eA⟩, ⟨eB⟩, hAB2⟩ := h
  have hAB := le_centralizer_of_commute hcomm
  have hA8 : Nat.card A = 8 := by rw [Nat.card_congr eA.toEquiv, card_quaternion_two]
  have hB8 : Nat.card B = 8 := by rw [Nat.card_congr eB.toEquiv, card_quaternion_two]
  have hprod := card_sup_mul_card_inf_of_le_centralizer hAB
  rw [hgen, Subgroup.card_top, hAB2, hA8, hB8] at hprod
  exact ⟨by omega, A, B, ⟨hAB, hgen⟩, ⟨eA⟩, ⟨eB⟩⟩

theorem exists_surjective_ker_isQ8Sq_of_isExtensionWith {X Y : Type*} [Group X] [Finite X] [Group Y]
    (e : X ≃* Y)
    (h : F6.IsExtensionWith X (DihedralGroup 6)
      (fun N => F6.IsCentralProduct₂ ↥N (QuaternionGroup 2) (QuaternionGroup 2))) :
    ∃ φ : Y →* DihedralGroup 6, Function.Surjective φ ∧ IsQ8Sq ↥φ.ker := by
  obtain ⟨φ, hφ, hker⟩ := h
  refine ⟨φ.comp e.symm.toMonoidHom, hφ.comp e.symm.surjective, ?_⟩
  have hQ : IsQ8Sq ↥φ.ker := isQ8Sq_of_centralProduct₂ hker
  have hk : (φ.comp e.symm.toMonoidHom).ker = φ.ker.map e.toMonoidHom := by
    ext y
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨e.symm y, hy, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  rw [hk]
  exact IsQ8Sq.of_mulEquiv (e.subgroupMap φ.ker) hQ

end CFSG.Quasithin
