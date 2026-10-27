module

public import CFSG.Quasithin.Vol2.Ch11SecAKE16
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112NotLie
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Local
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.QuasithinUnique C10KH

@[expose] def FactOuterLeviL225 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsPSL 2 5 2 S →
    ∀ R B : Subgroup S, QuasithinUnique.IsSylowTwoOf R ⊤ →
      R ≤ Subgroup.normalizer (B : Set S) → ⁅B, B⁆ = B →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      ∃ r ∈ R, ∀ b ∈ B, ∃ y ∈ B, r * y * r⁻¹ * (b * y * b⁻¹)⁻¹ ∉ pCoreOf 2 B


theorem factOuterLeviL225_holds : FactOuterLeviL225 := by
  intro S _ _ hS R B hR hRB hB hF
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF4, ⟨eF⟩⟩ := hF
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := 2) Nat.prime_two (by norm_num) (by rw [hF4]; norm_num)
  have hS7800 : Nat.card S = 7800 := by
    rw [H13.NotLie.card_psl2 hS]
    norm_num
  obtain ⟨-, K, _, _, hK, ⟨eS⟩⟩ := hS
  let e : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    eS.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hq60 : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 60 := by
    rw [Nat.card_congr eF.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF4]
    norm_num
  have hBperf : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hB
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).exists_card_eq
  have hcB : Nat.card B = 60 * 2 ^ k := by
    rw [(CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup, hq60, hk]
  have hBnt : Nontrivial ↥B := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcB]
    have := Nat.one_le_two_pow (n := k)
    omega
  have hBns : ¬ Group.IsSolvable ↥B := Group.IsPerfect.not_isSolvable ↥B
  have hB60 : Nat.card B = 60 := by
    have hcm : Nat.card ↥(B.map e.toMonoidHom) = Nat.card B :=
      Subgroup.card_map_of_injective e.injective
    have eBm := B.equivMapOfInjective e.toMonoidHom e.injective
    have hns' : ¬ Group.IsSolvable ↥(B.map e.toMonoidHom) := fun h => hBns
      (Group.isSolvable_of_isSolvable_injective (f := eBm.toMonoidHom) eBm.injective)
    rcases psl225_subgroup hK _ hns' with h | h | ⟨-, ⟨ePGL⟩⟩
    · rwa [hcm] at h
    · exfalso
      rw [hcm, hcB] at h
      have h130 : 2 ^ k = 130 := by omega
      have hk8 : k < 8 := by
        by_contra hh
        have : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases k <;> omega
    · exfalso
      have : Group.IsPerfect ↥(B.map e.toMonoidHom) :=
        Group.IsPerfect.ofSurjective (f := eBm.toMonoidHom) eBm.surjective
      exact CFSG.RankThree.SubgroupLists.not_isPerfect_pgl2
        (by rw [ringChar.eq (GaloisField 5 1) 5]; norm_num)
        (Group.IsPerfect.ofSurjective (f := ePGL.toMonoidHom) ePGL.surjective)
  have hO1 : CFSG.pCore 2 ↥B = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rw [hk]
    have : 2 ^ k = 1 := by omega
    exact this
  obtain ⟨eA⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
    (Or.inl hF4)
  let eB : ↥B ≃* alternatingGroup (Fin 5) :=
    ((((QuotientGroup.quotientBot (G := ↥B)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hO1.symm)).trans eF).trans
        Vol2Native.A312L.sl2EquivStatedProj).trans eA
  have hZ : ∀ z ∈ B, (∀ y ∈ B, z * y = y * z) → z = 1 := by
    intro z hz hzy
    have h1 : eB ⟨z, hz⟩ = 1 := a5_center _ fun y => by
      obtain ⟨⟨w, hw⟩, rfl⟩ := eB.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg eB (Subtype.ext (hzy w hw))
    have := congrArg Subtype.val (eB.injective (h1.trans (map_one eB).symm))
    exact this
  have hexp : ∀ x ∈ B, x ^ 8 = 1 → x ^ 2 = 1 := by
    intro x hx h8
    have h1 : eB ⟨x, hx⟩ ^ 2 = 1 := a5_pow_eight _ (by
      rw [← map_pow, show (⟨x, hx⟩ : ↥B) ^ 8 = 1 from Subtype.ext h8, map_one])
    rw [← map_pow, ← map_one eB] at h1
    exact congrArg Subtype.val (eB.injective h1)
  have hpc : pCoreOf 2 B = ⊥ := by
    rw [pCoreOf, hO1, Subgroup.map_bot]
  have hR8 : Nat.card R = 8 := card_sylow_of_card_7800 hS7800 hR
  have hRe : QuasithinUnique.IsSylowTwoOf (R.map e.toMonoidHom) ⊤ :=
    CFSG.Quasithin.A312.isSylowTwoOf_top_map e.toMonoidHom e.surjective hR
  obtain ⟨x', hx', y', hy', hxy'⟩ := sylow_nonabelian hK hRe
  obtain ⟨x, hx, rfl⟩ := hx'
  obtain ⟨y, hy, rfl⟩ := hy'
  have hxy : x * y ≠ y * x := fun h => hxy' (by rw [← map_mul, ← map_mul, h])
  have hRexp : ∀ z ∈ R, z ^ 8 = 1 := fun z hz => by
    have h : (⟨z, hz⟩ : R) ^ Nat.card R = 1 := pow_card_eq_one'
    rw [hR8] at h
    exact congrArg Subtype.val h
  have hidx : (B.subgroupOf R).index = 2 := by
    have h1 : B.relIndex (R ⊔ B) = B.relIndex R :=
      CFSG.QuasithinUnique.A3Gen.relIndex_sup_eq_of_le_normalizer' hRB
    have h2 := Subgroup.relIndex_mul_card (H := B) (K := R ⊔ B)
    rw [inf_eq_left.mpr le_sup_right, hB60] at h2
    have h3 := Subgroup.relIndex_mul_card (H := B) (K := R)
    rw [hR8] at h3
    have h4 : Nat.card ↥(R ⊔ B) ∣ 7800 := hS7800 ▸ Subgroup.card_subgroup_dvd_card _
    have hRB' : ¬ R ≤ B := fun hle => by
      have := Subgroup.card_dvd_of_le hle
      rw [hR8, hB60] at this
      norm_num at this
    have h5 : B.relIndex R ≠ 1 := fun h => hRB' (Subgroup.relIndex_eq_one.mp h)
    show B.relIndex R = 2
    rw [← h1] at h3 h5
    rw [← h1]
    generalize B.relIndex (R ⊔ B) = n at h2 h3 h5 h4 ⊢
    obtain ⟨d, hd⟩ := h4
    rw [← h2] at hd
    have hd8 : n ∣ 8 := ⟨_, h3.symm⟩
    have hd130 : n ∣ 130 := ⟨d, by
      have h7 : 60 * 130 = 60 * (n * d) := by
        calc 60 * 130 = 7800 := by norm_num
          _ = n * 60 * d := hd
          _ = 60 * (n * d) := by ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h7⟩
    have hle := Nat.le_of_dvd (by norm_num) hd8
    interval_cases n <;> first | rfl | (exfalso; omega)
  by_contra hcon
  push Not at hcon
  refine hxy (comm_of_inner hR hRB hZ hexp hRexp hidx (fun r hr => ?_) x hx y hy)
  obtain ⟨b, hb, hby⟩ := hcon r hr
  refine ⟨b, hb, fun z hz => ?_⟩
  have h1 := hby z hz
  rw [hpc, Subgroup.mem_bot] at h1
  exact mul_inv_eq_one.mp h1

@[expose] def FactOuterLeviL35U35 : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (IsSLEps3 true 5 S ∨ IsPSLEps3 true 5 1 S ∨ IsPSLEps3 false 5 1 S) →
    ∀ R B : Subgroup S, QuasithinUnique.IsSylowTwoOf R ⊤ →
      R ≤ Subgroup.normalizer (B : Set S) → ⁅B, B⁆ = B →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      ∃ r ∈ R, ∀ b ∈ B, ∃ y ∈ B, r * y * r⁻¹ * (b * y * b⁻¹)⁻¹ ∉ pCoreOf 2 B

theorem factOuterLevi_of_cases (h1 : FactOuterLeviL225) (h2 : FactOuterLeviL35U35) :
    FactOuterLevi := by
  intro S _ _ hS
  rcases hS with h | h
  · exact h1 S h
  · exact h2 S h

end CFSG.Quasithin.Vol2.Ch11.SecA
