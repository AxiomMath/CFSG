module

public import CFSG.RankThree.PartTwo.Sec14.Item14J2
public import CFSG.Sporadic.Bridge.J2
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasicCertificate13952Inputs

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG CFSG.Blueprint
open scoped commutatorElement

theorem card_nativeJ2 : Nat.card NativeSporadic.J2 = 604800 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  refine le_antisymm ?_ ?_
  · rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Bridge.J2.tauCeti_finite_card_le.2
  · rw [Nat.card_congr CFSG.Sporadic.Bridge.J2.nativeEquiv.toEquiv]
    exact CFSG.Sporadic.Bridge.J2.le_card_seedGroup

theorem card_eq_of_j2 {X : Type*} [Group X] (hX : Nonempty (X ≃* NativeSporadic.J2)) :
    Nat.card X = 604800 := by
  obtain ⟨e⟩ := hX
  rw [Nat.card_congr e.toEquiv, card_nativeJ2]

theorem m24W_mem : m24W ∈ NativeSporadic.M24 := by
  unfold m24W
  have ha : m24A ∈ NativeSporadic.M24 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : m24B ∈ NativeSporadic.M24 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hbi := inv_mem hb
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (mul_mem (mul_mem ha hb) ha) hb) ha) hb) ha) hbi) ha) hbi) ha) hbi

theorem not_eleven_dvd_card_of_j2 {X : Type*} [Group X] (hX : Nonempty (X ≃* NativeSporadic.J2)) :
    ¬ 11 ∣ Nat.card X := by
  rw [card_eq_of_j2 hX]
  norm_num

section Center

variable {X : Type} [Group X] [Finite X]

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_eq_of_isExtOf_alternating_six {Y : Type*} [Group Y]
    (h : Sec4.IsExtOf Y (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3))) :
    Nat.card Y = 1080 := by
  obtain ⟨K, hKn, ⟨eK⟩, ⟨eQ⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, Nat.card_congr eQ.toEquiv,
    Nat.card_congr eK.toEquiv, card_alternatingGroup_six, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card]

theorem mem_of_mem_center_of_isExtOf {Y : Type*} [Group Y] {K : Subgroup Y} [K.Normal]
    (eQ : Y ⧸ K ≃* alternatingGroup (Fin 6)) {y : Y} (hy : y ∈ Subgroup.center Y) : y ∈ K := by
  have hcen : QuotientGroup.mk' K y ∈ Subgroup.center (Y ⧸ K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective K q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hy w]
  rw [Sec14.center_eq_bot_of_mulEquiv_alternating_six eQ, Subgroup.mem_bot,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  exact hcen

theorem center_eq_bot_of_j2 (h415 : Sec4.Item4_15) (hX : Nonempty (X ≃* NativeSporadic.J2)) :
    Subgroup.center X = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 X) := inferInstance
  obtain ⟨h3, -, hext⟩ := Sec14.j2_sylow_facts h415 hX P
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZ
  set C := Subgroup.centralizer (Z : Set X) with hC
  have hC1080 : Nat.card C = 1080 := card_eq_of_isExtOf_alternating_six hext
  obtain ⟨K, hKn, ⟨eK⟩, ⟨eQ⟩⟩ := hext
  have hK3 : Nat.card K = 3 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  have hcC : Subgroup.center X ≤ C := fun g hg =>
    Subgroup.mem_centralizer_iff.mpr fun h _ => Subgroup.mem_center_iff.mp hg h
  have hcK : (Subgroup.center X).subgroupOf C ≤ K := by
    intro g hg
    refine mem_of_mem_center_of_isExtOf eQ (Subgroup.mem_center_iff.mpr fun y => ?_)
    exact Subtype.ext (Subgroup.mem_center_iff.mp (Subgroup.mem_subgroupOf.mp hg) y)
  have hdvd : Nat.card (Subgroup.center X) ∣ 3 := by
    rw [← hK3, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcC).toEquiv]
    exact Subgroup.card_dvd_of_le hcK
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3c
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have hp : IsPGroup 3 (Subgroup.center X) := IsPGroup.of_card (n := 1) (by rw [h3c, pow_one])
    have hcP : Subgroup.center X ≤ P := hp.le_sylow_of_normal P
    have hcZ : Subgroup.center X ≤ Z := fun g hg =>
      ⟨hcP hg, Subgroup.mem_centralizer_iff.mpr fun h _ => Subgroup.mem_center_iff.mp hg h⟩
    have hceq : Subgroup.center X = Z :=
      Subgroup.eq_of_le_of_card_ge hcZ (by rw [h3, h3c])
    have hCtop : C = ⊤ := by
      rw [hC, ← hceq]
      exact Subgroup.centralizer_eq_top_iff_subset.mpr fun g hg =>
        Subgroup.mem_center_iff.mpr fun h => (Subgroup.mem_center_iff.mp hg h)
    have := card_eq_of_j2 hX
    rw [← Subgroup.card_top (G := X), ← hCtop, hC1080] at this
    norm_num at this

theorem center_nativeJ2_eq_bot (h415 : Sec4.Item4_15) : Subgroup.center NativeSporadic.J2 = ⊥ :=
  center_eq_bot_of_j2 h415 ⟨MulEquiv.refl _⟩

end Center

section ENine

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem conjugate_conjugate_eq_mul (H : Subgroup X) (x y : X) :
    conjugate (conjugate H x) y = conjugate H (x * y) := by
  rw [conjugate, conjugate, conjugate, Subgroup.map_map]
  congr 1
  ext g
  simp [mul_assoc]

theorem j2_inf_centralizer_le_of_card_nine (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* NativeSporadic.J2)) (P : Sylow 3 X) {E : Subgroup X}
    (hEP : E ≤ P) (hE9 : Nat.card E = 9) :
    (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) ≤ E := by
  obtain ⟨⟨hHeis, -⟩, -⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨⟨-, hcomm, -, -⟩, h27, -⟩ := hHeis
  set E' := E.subgroupOf (P : Subgroup X) with hE'
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hE9]
  have hidx : E'.index = 3 := by
    have h := E'.card_mul_index
    rw [hE'9, h27] at h
    omega
  have hnorm : E'.Normal := Subgroup.normal_of_index_eq_minFac_card (by
    rw [hidx, h27]
    norm_num)
  have hQ3 : Nat.card (↥(P : Subgroup X) ⧸ E') = 3 := by
    rw [← Subgroup.index_eq_card, hidx]
  have hQcomm : ∀ q r : ↥(P : Subgroup X) ⧸ E', q * r = r * q := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcyc : IsCyclic (↥(P : Subgroup X) ⧸ E') := isCyclic_of_prime_card hQ3
    intro q r
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg q)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg r)
    exact zpow_mul_comm g m n
  have hcle : commutator ↥(P : Subgroup X) ≤ E' := by
    rw [commutator_def, Subgroup.commutator_le]
    intro p _ q _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' E' ⁅p, q⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hQcomm _ _
  rw [hcomm] at hcle
  intro z hz
  have hzc : (⟨z, hz.1⟩ : ↥(P : Subgroup X)) ∈ Subgroup.center ↥(P : Subgroup X) := by
    rw [← Sec14.map_subtype_center_eq] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have : w = ⟨z, hz.1⟩ := Subtype.ext hwz
    rw [← this]
    exact hw
  exact Subgroup.mem_subgroupOf.mp (hcle hzc)

theorem j2_exists_sylow_of_card_nine (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* NativeSporadic.J2)) {E : Subgroup X} (hE9 : Nat.card E = 9) :
    ∃ P : Sylow 3 X, E ≤ P ∧
      (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) ≤ E ∧
      E ≤ Subgroup.centralizer
        (((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) : Subgroup X) :
          Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  obtain ⟨P, hEP⟩ := hp.exists_le_sylow
  refine ⟨P, hEP, j2_inf_centralizer_le_of_card_nine h415 hX P hEP hE9, fun e he => ?_⟩
  exact Subgroup.mem_centralizer_iff.mpr fun z hz =>
    (Subgroup.mem_centralizer_iff.mp hz.2 e (hEP he)).symm

theorem j2_exists_conjugate_of_card_nine (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* NativeSporadic.J2)) {E E' : Subgroup X} (hE : Nat.card E = 9)
    (hE' : Nat.card E' = 9) : ∃ g : X, E' = conjugate E g := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE]; norm_num)
  have hp' : IsPGroup 3 E' := IsPGroup.of_card (n := 2) (by rw [hE']; norm_num)
  obtain ⟨P, hEP⟩ := hp.exists_le_sylow
  obtain ⟨Q, hE'Q⟩ := hp'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Q
  have hQ : (Q : Subgroup X) = (P : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sec14.coe_sylow_smul_eq_map]
  have hle : conjugate E' g ≤ P := by
    rw [conjugate]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hQ] at hE'Q
    obtain ⟨w, hw, hwy⟩ := hE'Q hy
    rw [← hwy]
    have hc : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom w) = w := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [hc]
    exact hw
  have hcard : Nat.card (conjugate E' g) = 9 := by
    rw [conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hE']
  obtain ⟨-, htrans, -⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨x, -, hx⟩ := htrans E ⟨hEP, hE⟩ (conjugate E' g) ⟨hle, hcard⟩
  refine ⟨x * g⁻¹, ?_⟩
  rw [← conjugate_conjugate_eq_mul, ← hx, conjugate_conjugate_eq_mul, mul_inv_cancel]
  ext y
  simp [conjugate]

end ENine

end CFSG.RankThree.PartTwo.KFacts.KS14
